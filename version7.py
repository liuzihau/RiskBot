from collections import defaultdict, deque
import random
from typing import Optional, Tuple, Union, cast
from risk_helper.game import Game
from risk_shared.models.card_model import CardModel
from risk_shared.queries.query_attack import QueryAttack
from risk_shared.queries.query_claim_territory import QueryClaimTerritory
from risk_shared.queries.query_defend import QueryDefend
from risk_shared.queries.query_distribute_troops import QueryDistributeTroops
from risk_shared.queries.query_fortify import QueryFortify
from risk_shared.queries.query_place_initial_troop import QueryPlaceInitialTroop
from risk_shared.queries.query_redeem_cards import QueryRedeemCards
from risk_shared.queries.query_troops_after_attack import QueryTroopsAfterAttack
from risk_shared.queries.query_type import QueryType
from risk_shared.records.moves.move_attack import MoveAttack
from risk_shared.records.moves.move_attack_pass import MoveAttackPass
from risk_shared.records.moves.move_claim_territory import MoveClaimTerritory
from risk_shared.records.moves.move_defend import MoveDefend
from risk_shared.records.moves.move_distribute_troops import MoveDistributeTroops
from risk_shared.records.moves.move_fortify import MoveFortify
from risk_shared.records.moves.move_fortify_pass import MoveFortifyPass
from risk_shared.records.moves.move_place_initial_troop import MovePlaceInitialTroop
from risk_shared.records.moves.move_redeem_cards import MoveRedeemCards
from risk_shared.records.moves.move_troops_after_attack import MoveTroopsAfterAttack
from risk_shared.records.record_attack import RecordAttack
from risk_shared.records.types.move_type import MoveType

import heapq

VERSION = '7.0.0'
DEBUG = False

CONTINENT = {
    "AU": [38, 39, 41, 40],
    "SA": [28, 31, 29, 30],
    "AF": [35, 37, 32, 33, 36, 34],
    "EU": [12, 10, 9, 15, 13, 14, 11],
    "NA": [5, 4, 0, 1, 6, 7, 8, 3, 2],
    "AS": [20, 27, 21, 25, 26, 19, 23, 17, 24, 18, 22, 16]
    }

PREFER = {
    "AU": 0.05,
    "SA": 0.04,
    "AF": 0.03,
    "NA": 0.01,
    "EU": -0.4,
    "AS": -0.6
    }

DOOR = {
    "AU": [40],
    "SA": [29, 30],
    "AF": [33, 36, 34],
    "EU": [10, 15, 13, 14],
    "NA": [4, 0, 2],
    "AS": [21, 26, 24, 22, 16]
}

REWARD = {
        "AU" : 2,
        "SA" : 2,
        "AF" : 3,
        "EU" : 5,
        "NA" : 5,
        "AS" : 7
    }

DIFF = {
    0:5,
    1:5,
    2:3,
    3:1
}

# help function
def write_log(game, msg):
    if DEBUG:
        with open(game.log, 'a') as f:
            f.write(f"{msg}\n")
    else:
        print(msg, flush=True)

def group_connected_territories(mt, state):
    def DFS_visit(k):
        visited[k] = True 
        for v in state.map.get_adjacent_to(k):
            if v in visited and not visited[v]:
                parent[v] = u
                group.append(v)
                DFS_visit(v)

    visited, parent = {}, {}
    for u in mt:
        visited[u], parent[u] = False, None
    groups = []
    for u in mt:
        group = [u]
        if not visited[u]:
            DFS_visit(u)
            groups.append(group)
    return groups 

def get_percentage_to_continent(mt, name):
    return len(set(CONTINENT[name]) & set(mt))/len(CONTINENT[name])


def find_shortest_path_from_vertex_to_vertex_via_group(state, source: int, target: int, group: list) -> list[int]:
    queue = deque()
    queue.appendleft(source)
    parent = {}
    seen = {queue[0]:True}

    while len(queue) != 0:
        current = queue.pop()
        if current == target:
            break
        neighbours = list(set(state.map.get_adjacent_to(current)) & set(group))
        for neighbour in neighbours:
            if neighbour not in seen:
                seen[neighbour] = True
                parent[neighbour] = current
                queue.appendleft(neighbour)
    path = []
    while current in parent:
        path.append(current)
        current = parent[current]
    path.append(current)
    return path[::-1]

def dijkstra(state, source: int, targets: list, enemy_territories) -> tuple:
    # Initialize the priority queue
    pq = []
    distances = {vertex: float('infinity') for vertex in enemy_territories}
    previous_vertices = {source:None}

    # Set the distance for start vertices
    distances[source] = 0
    heapq.heappush(pq, (0, source))

    while pq:
        current_distance, current_vertex = heapq.heappop(pq)

        # If we reach a target vertex, we can return the path and distance
        for target in targets:
            if current_vertex in target:
                path = []
                while current_vertex is not None:
                    path.append(current_vertex)
                    current_vertex = previous_vertices[current_vertex]
                return path[::-1], current_distance, target

        # Process each neighbor
        neighbors = list(set(state.map.get_adjacent_to(current_vertex)) & set(enemy_territories))

        for neighbor in neighbors:
            distance = current_distance + state.territories[neighbor].troops
            # Only consider this new path if it's better
            if distance < distances[neighbor]:
                distances[neighbor] = distance
                previous_vertices[neighbor] = current_vertex
                heapq.heappush(pq, (distance, neighbor))

    return None, float('infinity'), None




class Bot:
    def __init__(self, state, log):
        self.state = state
        self.log = log
        self.id_me = None
        self.ids_others = []
        self.territories = {}
        self.adjacent_territories = []
        self.border_territories = []
        self.plan = None
        self.got_territoty_this_turn = False
        self.clock = 0


    def update_status(self):
        if self.id_me is None:
            self.id_me = self.state.me.player_id
            self.ids_others = list({0, 1, 2, 3, 4} - {self.id_me})
        self.territories[None] = self.state.get_territories_owned_by(None)
        self.territories[self.id_me] = self.state.get_territories_owned_by(self.id_me)
        for pid in self.ids_others:
            self.territories[pid] = self.state.get_territories_owned_by(pid)
        self.adjacent_territories = self.state.get_all_adjacent_territories(self.territories[self.id_me])
        self.border_territories = self.state.get_all_border_territories(self.territories[self.id_me])

    def plan_to_do(self):
        """
        plan_dict
        {
                        "code": 0,
                        "name": name,
                        "from": pair[0],
                        "to": pair[1],
                        "cost":cost,
                        "diff":diff,
                        "reward": REWARD[name]
                        }
        """
        if self.plan is None:
            occupy_plan_list = self.occupy_new_continent()
            kill_plan_list = self.kill_player()
            interupt_plan_list = self.interupt_opponunt_continent()

            # strategic attack for future
            minimum_attack_list = self.minimum_attack()

            if kill_plan_list is not None and occupy_plan_list is not None:
                killing_reward = kill_plan_list[0]['reward'] * 3 - kill_plan_list[0]['cost']
                occupy_reward = occupy_plan_list[0]['reward'] * 3 - occupy_plan_list[0]['cost']
                if killing_reward > occupy_reward and killing_reward > 0:
                    self.plan = kill_plan_list[0]
                    write_log(self.log, f"[#{self.clock}][Plan] killing path for player{kill_plan_list[0]['pid']} :{kill_plan_list[0]}, total cost = {kill_plan_list[0]['cost']}")
                    return
                elif occupy_reward >= killing_reward and occupy_reward > 0:
                    self.plan = occupy_plan_list[0]
                    write_log(self.log, f"[#{self.clock}][Plan] choose occupy plan {occupy_plan_list[0]}")
                    return
            
            elif kill_plan_list is not None:
                killing_reward = kill_plan_list[0]['reward'] * 3 - kill_plan_list[0]['cost']
                if killing_reward > 0:
                    self.plan = kill_plan_list[0]
                    write_log(self.log, f"[#{self.clock}][Plan] killing path for player{kill_plan_list[0]['pid']} :{kill_plan_list[0]}, total cost = {kill_plan_list[0]['cost']}")
                    return

            elif occupy_plan_list is not None:
                self.plan = occupy_plan_list[0]
                write_log(self.log, f"[#{self.clock}][Plan] choose occupy plan {occupy_plan_list[0]}")
                return
            
            if minimum_attack_list is not None:
                self.plan = minimum_attack_list[0]
                write_log(self.log, f"[#{self.clock}][Plan] choose minimum attack plan {minimum_attack_list[0]}")

            return
        
        src = self.state.territories[self.plan["from"]].troops
        tgt = self.state.territories[self.plan["to"]].troops
        if (src > tgt + 3) or (src > tgt and tgt > 20):
            return
        
        if self.plan["code"] == 0:
            occupy_plan_list = self.occupy_new_continent()
            if occupy_plan_list is not None:
                self.plan = occupy_plan_list[0]
                return
        elif self.plan["code"] == 1:
            interupt_plan_list = self.interupt_opponunt_continent()
            if interupt_plan_list is not None:
                self.plan = interupt_plan_list[0]
                return
        elif self.plan["code"] == 2:
            minimum_attack_list = self.minimum_attack()
            if minimum_attack_list is not None:
                self.plan = minimum_attack_list[0]
                return
        elif self.plan["code"] == 3:
            kill_plan_list = self.kill_player()
            if kill_plan_list is not None:
                self.plan = kill_plan_list[0]
                return
        self.plan = None

    
    def find_border_territories_inside_continent(self, name):
        continent_plus_adj = set(CONTINENT[name]) | set(self.state.get_all_adjacent_territories(CONTINENT[name]))
        my_effective_territoies = list(set(self.territories[self.id_me]) & continent_plus_adj)
        border_territories = []
        for territory in my_effective_territoies:
            adj_territories = self.state.map.get_adjacent_to(territory)
            adj_in_continent = list(set(CONTINENT[name]) & set(adj_territories))
            for adj_territory in adj_in_continent:
                if self.state.territories[adj_territory].occupier != self.id_me:
                    border_territories.append(territory)
                    break
        return border_territories
    
    def find_good_attack_source_and_target(self, enemy_territories, border_territories):
        pair = []
        for my_territory in border_territories:
            adj_territories = self.state.map.get_adjacent_to(my_territory)
            adj_in_continent = list(set(enemy_territories) & set(adj_territories))
            for adj_territory in adj_in_continent:
                my_troops = self.state.territories[my_territory].troops
                enemy_troops = self.state.territories[adj_territory].troops
                diff = my_troops - 1 - enemy_troops
                dice = min(3, my_troops - 1)
                if diff > 0:
                    pair.append((my_territory, adj_territory, diff, dice))
        pair = sorted(pair, key=lambda x: (x[2], x[3]), reverse=True)
        if len(pair) > 0:
            return pair[0]

    def occupy_new_continent(self):
        """
        find my border territories in the continent and
        """
        if self.plan is not None:
            name_list = [self.plan['name']]
        else:
            name_list = CONTINENT
        plan_list = []
        for name in name_list:
            enemy_territories = list(set(CONTINENT[name]) - set(self.territories[self.id_me]))
            if len(enemy_territories) == 0:
                return
            border_territories = self.find_border_territories_inside_continent(name)
            if border_territories is None:
                continue
            enemy_troops = self.enemy_troops_in_continent(name)
            if enemy_troops == 0:
                continue
            my_effect_troops = self.my_effect_troops_in_continent(name, border_territories)
            cost = enemy_troops + len(enemy_territories)
            diff = my_effect_troops - enemy_troops
            if diff + self.state.me.troops_remaining < 1:
                continue
            pair = self.find_good_attack_source_and_target(enemy_territories, border_territories)
            if pair is not None:
                plan_list.append(
                    {
                        "code": 0,
                        "name": name,
                        "from": pair[0],
                        "to": pair[1],
                        "cost":cost,
                        "diff":diff,
                        "reward": REWARD[name]
                        }
                )
        if len(plan_list) > 0:
            return plan_list
        return
    
    def kill_player(self):
        if self.plan is not None:
            pid_list = [self.plan["pid"]]
        else:
            pid_list = self.ids_others

        plan_list = []
        reward_weight = self.clock / 2000
        for pid in pid_list:
            killing_path = self.find_killing_path(pid)
            if killing_path is not None:
                total_cost = 0
                total_diff = 0
                for r in killing_path:
                    total_cost += r["cost"]
                    if r['diff'] < 1:
                        total_diff -= (r["diff"]+1)
                plan_list.append(
                    {
                        "code":3,
                        "name":None,
                        "from":killing_path[0]['path'][0],
                        "to":killing_path[0]['path'][1],
                        "cost":total_cost,
                        "diff":total_diff,
                        "reward":reward_weight * self.state.players[pid].card_count,
                        "route":killing_path,
                        "pid":pid
                    }
                )
        if len(plan_list) > 0:
            return plan_list
        
    def find_killing_path(self, target_id):
        enemy_territories = set()
        for pid in self.ids_others:
            enemy_territories = enemy_territories | set(self.territories[pid])
        enemy_territories = list(enemy_territories)

        target_groups = group_connected_territories(self.territories[target_id], self.state)
        route = self.find_shortest_cost_from_group_to_group(self.border_territories, target_groups, enemy_territories)
        if route is not None:
            troops_needed = 0
            for sub_route in route:
                sub_route["diff"] = sub_route['path'][0] - sub_route["cost"] - len(sub_route['path'] + sub_route['target'])
                if sub_route["diff"] < 1:
                    troops_needed -= (sub_route['diff'] - 1)
            if self.state.me.troops_remaining > troops_needed:
                return route

    def find_shortest_cost_from_group_to_group(self, sources: list, targets: list, enemy_territories) -> Union[list[int], None]:
        route = []
        while len(targets) > 0:
            paths = []
            for source in sources:
                path, cost, target = dijkstra(self.state, source, targets, enemy_territories)
                if path is None:
                    continue
                for tid in target:
                    cost += self.state.territories[tid].troops
                paths.append(
                    {
                        "path":path,
                        "cost":cost,
                        "target":target
                                }
                )
            chosen_path = min(paths, key=lambda x:x['cost'])
            route.append(chosen_path)
            targets.remove(chosen_path["target"])
            sources = list(set(sources) | set(chosen_path["path"]) | set(chosen_path["target"]))
            enemy_territories = list(set(enemy_territories) - set(sources))
        
        if len(route) > 0:
            return route
        
    def interupt_opponunt_continent(self):
        pass

    def minimum_attack(self):
        if self.got_territoty_this_turn:
            return
        plan_list = []
        for tid in self.border_territories:
            current_territory = self.state.territories[tid]
            candidates = self.state.map.get_adjacent_to(tid)
            for cid in candidates:
                adjacent_territory = self.state.territories[cid]
                if adjacent_territory.occupier == self.id_me:
                    continue
                cost = adjacent_territory.troops
                diff = current_territory.troops - cost - 1
                if diff + self.state.me.troops_remaining < 2:
                    continue
                for name in CONTINENT:
                    if cid in CONTINENT[name]:
                        plan_list.append(
                            {
                        "code": 2,
                        "name": name,
                        "from": tid,
                        "to": cid,
                        "cost":cost,
                        "diff":diff,
                        "reward": 0
                        }
                )
        if len(plan_list):
            return sorted(plan_list, key=lambda x:x['cost'])
        return 

    # Claim Territories
    def choose_adjacent_with_info(self, info):
        territories = list(set(self.adjacent_territories) & set(info))
        if territories:
            return territories[0]
        return info[0]
    
    def block_players(self):
        risk_list = self.check_continent_occupy_risk()
        if len(risk_list) > 0:
            continent_name = sorted(risk_list, key=lambda x:x[1])[-1][0]
            block_territories = list(set(CONTINENT[continent_name]) & set(self.territories[None]))
            if len(block_territories) > 0:
                return block_territories[0]
        return None
    
    def get_sorted_connected_group(self):
        groups = group_connected_territories(self.territories[self.id_me], self.state)
        return sorted(groups, key=lambda x:len(x), reverse=True)
    
    def try_to_connect_territory_no_gap(self, sorted_groups):
        # need to adjacent and g > 1
        for g in sorted_groups:
            if len(g) == 1:
                break
            possible_territories = list(set(self.state.get_all_adjacent_territories(g)) & set(self.territories[None]))
            if len(possible_territories) > 0:
                return possible_territories[0]
        return None
    
    def try_to_connect_territory_1_gap(self, sorted_groups):  
        # try accept 1 gap
        for g in sorted_groups:
            gapped = set(self.state.get_all_adjacent_territories(g)) | set(g)
            possible_territories = list(gapped & set(self.territories[None]))
            if len(possible_territories) > 0:
                return possible_territories[0]
        return None
    
    def pick_by_degree(self):
        # means we can't find connected land
        selected_territory = sorted(self.territories[None], key=lambda x: len(self.state.map.get_adjacent_to(x)), reverse=True)[0]
        return selected_territory
    
    def check_continent_occupy_risk(self):
        risk_list = []
        for pid in self.ids_others:
            for name in ['AU', 'SA', 'AF']:
                pr_current = get_percentage_to_continent(self.territories[pid], name)
                pr_potential = get_percentage_to_continent(self.territories[None], name)
                if pr_current + pr_potential >= 0.9 and pr_current > 0.61:
                    risk_list.append((name, pr_current+pr_potential))
        return risk_list
    
    def search_preferred_continent(self):
        pr_list = self.check_continent_availibility()
        if len(pr_list) > 0:
            prefered_name, pr = sorted(pr_list, key=lambda x:x[1])[-1]
            if pr >= 0.50:
                return list(set(self.territories[None]) & set(CONTINENT[prefered_name]))
        return None
    
    def check_continent_availibility(self):
        pr_list = []
        for name in ['AU', 'SA', 'AF', 'NA']:
            my_troops = self.my_troops_in_continent(name)
            enemy_troops = self.enemy_troops_in_continent(name)
            if my_troops < enemy_troops:
                continue
            pr_hold = get_percentage_to_continent(self.territories[self.id_me], name)
            pr_potential = get_percentage_to_continent(self.territories[None], name)
            pr_list.append((name, pr_hold + pr_potential + PREFER[name]))
        return pr_list

    def enemy_troops_in_continent(self, name):
        enemy_troops = 0
        candidate_territoies = CONTINENT[name]
        for tid in candidate_territoies:
            territory = self.state.territories[tid]
            if territory.occupier != self.id_me:
                enemy_troops += territory.troops
        return enemy_troops
    
    def my_troops_in_continent(self, name):
        my_troops = 0
        candidate_territoies = CONTINENT[name]
        for tid in candidate_territoies:
            territory = self.state.territories[tid]
            if territory.occupier == self.id_me:
                my_troops += territory.troops
        return my_troops
    
    def my_effect_troops_in_continent(self, name, border_territories):
        my_troops = 0
        for tid in border_territories:
            territory = self.state.territories[tid]
            if territory.troops > 3:  # we banned troops < 3 because we always want to roll 3 dices
                my_troops += territory.troops - 1  # -1 for the stay troop
        return my_troops

    # Put troops
    def put_troops_equally_on_border(self, group):
        borders = self.state.get_all_border_territories(group)
        return min(borders, key=lambda x:self.state.territories[x].troops)

    def check_full_control_continent(self):
        groups = self.get_sorted_connected_group()
        for name in CONTINENT:
            for g in groups:
                if get_percentage_to_continent(g, name) > 0.98:
                    return g
        return None
    
    def check_our_dominent_continent(self):
        pr_list = []
        for name in CONTINENT:
            pr = get_percentage_to_continent(self.territories[self.id_me], name)
            pr_list.append((name, pr))
        name = sorted(pr_list, key=lambda x:x[1])[-1][0]
        return list(set(CONTINENT[name]) & set(self.territories[self.id_me]))
    
    # Distribute troops
    def distribute_troops_by_plan(self, total_troops, distributions):
        if self.plan is not None:
            if self.plan["code"] == 3:
                for sub_route in self.plan["route"]:
                    if sub_route['diff'] < 1:
                        source = sub_route['path'][0]
                        diff = 0
                        found_new_source = False
                        while source not in self.territories[self.id_me]:
                            for s in self.plan["route"]:
                                if source in s['path'][1:]:
                                    source = s["path"][0]
                                    diff = diff + s['diff'] + sub_route['diff']
                                    found_new_source = True
                                    break
                            if not found_new_source:
                                break
                        if not found_new_source:
                            continue
                        else:
                            diff = sub_route['diff']
                        wanted_troops = (1 - diff)
                        got_troops = min(total_troops, wanted_troops)
                        distributions[sub_route["path"][0]] += got_troops
                        total_troops -= got_troops
                        write_log(self.log, f"[#{self.clock}][Distribute] distributed {got_troops} troops to territory {sub_route['path'][0]} by plan code {self.plan['code']}")
                    if total_troops == 0:
                        break
            else:
                need_troops = max(DIFF[self.plan["code"]] - self.plan["diff"], 0)
                distributed_troops = min(total_troops, need_troops)
                distributions[self.plan["from"]] += distributed_troops
                total_troops -= distributed_troops
                write_log(self.log, f"[#{self.clock}][Distribute] distributed {distributed_troops} troops to territory {self.plan['from']} by plan code {self.plan['code']}")
        return total_troops, distributions

    # Attack
    def attack_by_plan(self):
        if self.plan:
            return self.plan['from'], self.plan['to'], min(3, self.state.territories[self.plan['from']].troops - 1)
    
    # Troops after Attack
    def moving_troops_based_on_plan_code(self, record_attack, move_attack):
        src_territory = move_attack.attacking_territory
        tgt_territory = move_attack.defending_territory
        max_troops = self.state.territories[move_attack.attacking_territory].troops
        min_troops = move_attack.attacking_troops - record_attack.attacking_troops_lost

        if self.plan is None:
            return self.put_troops_on_border(src_territory, tgt_territory, max_troops, min_troops)
        if self.plan["code"] == 0:
            return self.put_troops_on_attack_territory(src_territory, tgt_territory, max_troops, min_troops)
        elif self.plan["code"] == 1:
            return max_troops - 1
        elif self.plan["code"] == 2:
            return max_troops - 1

    def put_troops_on_border(self, src, tgt, max_troops, min_troops):
        if src in self.border_territories and tgt in self.border_territories:
            write_log(self.log, f"[#{self.clock}][AfterAttack] {src} and {tgt} both are border, equally put troops {max(max_troops // 2, min_troops)}")
            return max(max_troops // 2, min_troops)
        elif tgt in self.border_territories:
            write_log(self.log, f"[#{self.clock}][AfterAttack] only {tgt} is border, put all troops {max_troops - 1}")
            return max_troops - 1
        else:
            write_log(self.log, f"[#{self.clock}][AfterAttack] only {src} is border or no border, put min troops {min_troops}")
            return min_troops
        
    def put_troops_on_attack_territory(self, src, tgt, max_troops, min_troops):
        if self.plan is None:
            return self.put_troops_on_border(src, tgt, max_troops, min_troops)
        potential_border = DOOR[self.plan["name"]]
        idle_troops = self.plan["diff"] - DIFF[self.plan["code"]]
        if src in potential_border:
            ideal_defend_troops = idle_troops // len(potential_border)
            final_troops = max(min_troops, min(max_troops - 1, ideal_defend_troops))
            write_log(self.log, f"[#{self.clock}][AfterAttack] trying occupy {DOOR[self.plan['name']]}, and {src} is door, put {final_troops} for protecting")
            return final_troops
        else:
            write_log(self.log, f"[#{self.clock}][AfterAttack] trying occupy {DOOR[self.plan['name']]}, and {src} is not door, put {min_troops}")
            return min_troops

    # Fortify
    def fortify_troops(self):
        tgt, group = self.find_weakest_territory()
        src, troops = self.find_strongest_territory(tgt, group)
        if src is not None and src != tgt:
            write_log(self.log, f"[#{self.clock}][Fortify] move from {src} to {set([tgt])} within our territories group {group} (our territoreis={self.state.get_territories_owned_by(self.id_me)})")
            path = find_shortest_path_from_vertex_to_vertex_via_group(self.state, src, tgt, group)
            return path[0], path[1], troops
        
    
    def find_weakest_territory(self):
        # check if we hold continent
        # find the group wtih continent and find the minimum border for the target
        # If we don't have continent, just choose the minimum border within the biggest group
        reward_pairs = sorted(REWARD.items(), key=lambda x:x[1], reverse=True)
        groups = self.get_sorted_connected_group()
        for name, reward in reward_pairs:
            if set(CONTINENT[name]) & set(self.territories[self.id_me]) != set(CONTINENT[name]):
                continue
            for group in groups:
                if set(CONTINENT[name]) & set(group) != set(CONTINENT[name]):
                    continue
                borders = list(set(group) & set(self.border_territories))
                write_log(self.log, f"[#{self.clock}][Fortify] find weakest border from {borders} in {group} (our territoreis={self.state.get_territories_owned_by(self.id_me)})")
                return min(borders, key=lambda x: self.state.territories[x].troops), group

        borders = list(set(groups[0]) & set(self.border_territories))
        return min(borders, key=lambda x: self.state.territories[x].troops), groups[0]
    
    def find_strongest_territory(self, weakest_territory, group):
        # first we check the largest troops we can use in the inner territories
        # second we check the maximum trrops we can use in the border territories
        # if split half the border the troops still safe and larger than inner troops than use border
        # use inner
        weakest_troops = self.state.territories[weakest_territory].troops

        inner_territories = list(set(group) - set(self.border_territories))
        if inner_territories:
            inner_territory = max(inner_territories, key=lambda x:self.state.territories[x].troops)
            inner_troop = self.state.territories[inner_territory].troops
        else:
            inner_territory = None
            inner_troop = 0

        border_territories = list(set(self.border_territories) & set(group))

        border_territories = sorted(border_territories, key=lambda x:self.state.territories[x].troops, reverse=True)
        for border_territory in border_territories:
            outer_troops = self.state.territories[border_territory].troops
            enemy_adj_territories = list(set(self.state.map.get_adjacent_to(border_territory)) - set(self.territories[self.id_me]))
            enemy_troops = 0
            for i in enemy_adj_territories:
                enemy_troops += self.state.territories[i].troops
            safe_moving = outer_troops - enemy_troops + 1 
            split_moving = (outer_troops - weakest_troops) // 2
            final_moving = min(safe_moving, split_moving)
            if final_moving > inner_troop - 1:
                return border_territory, final_moving
        return inner_territory, inner_troop - 1

        
# We will store our enemy in the bot state.
class BotState():
    def __init__(self):
        self.enemy: Optional[int] = None


def main():
    
    # Get the game object, which will connect you to the engine and
    # track the state of the game.
    game = Game()
    game.log = './log.txt'
    bot_state = BotState()
    bot = Bot(game.state, game.log) 
    game.bot = bot

    # Respond to the engine's queries with your moves.
    while True:

        # Get the engine's query (this will block until you receive a query).
        query = game.get_next_query()
        
        game.bot.clock = list(query.update.keys())[0]

        # Based on the type of query, respond with the correct move.
        def choose_move(query: QueryType) -> MoveType:
            match query:
                case QueryClaimTerritory() as q:
                    return handle_claim_territory(game, bot_state, q)

                case QueryPlaceInitialTroop() as q:
                    return handle_place_initial_troop(game, bot_state, q)

                case QueryRedeemCards() as q:
                    return handle_redeem_cards(game, bot_state, q)

                case QueryDistributeTroops() as q:
                    return handle_distribute_troops(game, bot_state, q)

                case QueryAttack() as q:
                    return handle_attack(game, bot_state, q)

                case QueryTroopsAfterAttack() as q:
                    return handle_troops_after_attack(game, bot_state, q)

                case QueryDefend() as q:
                    return handle_defend(game, bot_state, q)

                case QueryFortify() as q:
                    return handle_fortify(game, bot_state, q)
        
        # Send the move to the engine.
        game.bot.plan = None
        game.send_move(choose_move(query))
                

def handle_claim_territory(game: Game, bot_state: BotState, query: QueryClaimTerritory) -> MoveClaimTerritory:
    """
    At the start of the game, you can claim a single unclaimed territory every turn 
    until all the territories have been claimed by players.
    """

    # step 0 update status
    game.bot.update_status()

    # step 1 Blocking other player occupied whole continentcheck if other player have the chance to dominent one specific continent
    territory = game.bot.block_players()
    if territory:
        write_log(game, f"[#{game.bot.clock}][Claim] decided by block, {territory}")
        return game.move_claim_territory(query, territory)

    # step 2 check if we can dominent one specific continent
    territories = game.bot.search_preferred_continent()
    if territories:
        territory = game.bot.choose_adjacent_with_info(territories)
        write_log(game, f"[#{game.bot.clock}][Claim] decided by collect continent, {territory}")
        return game.move_claim_territory(query, territory)
    
    # step 3 try to maximise the adjacent territory
    sorted_group = game.bot.get_sorted_connected_group()
    territory = game.bot.try_to_connect_territory_no_gap(sorted_group)
    if territory:
        write_log(game, f"[#{game.bot.clock}][Claim] decided by connect with possible largest territories, {territory}")
        return game.move_claim_territory(query, territory)
    
    territory = game.bot.try_to_connect_territory_1_gap(sorted_group)
    if territory:
        write_log(game, f"[#{game.bot.clock}][Claim] decided by 1 gap with possible largest territories, {territory}")
        return game.move_claim_territory(query, territory)
    
    # step 4 pick by degree
    territory = game.bot.pick_by_degree()
    write_log(game, f"[#{game.bot.clock}][Claim] decided by degree, {territory}")
    return game.move_claim_territory(query, territory)

def handle_place_initial_troop(game: Game, bot_state: BotState, query: QueryPlaceInitialTroop) -> MovePlaceInitialTroop:
    """
    After all the territories have been claimed, you can place a single troop on one
    of your territories each turn until each player runs out of troops.
    """

    # step 0 update status
    game.bot.update_status()

    # senario 1: we control full continent
    group = game.bot.check_full_control_continent()
    if group:
        territory_id = game.bot.put_troops_equally_on_border(group)
        write_log(game.log, f"[#{game.bot.clock}][Initialise] equally distributed troops on the border of our continent {territory_id}")
        return game.move_place_initial_troop(query, territory_id)

    # senario 2: we have edge in a continent
    group = game.bot.check_our_dominent_continent()
    territory_id = game.bot.put_troops_equally_on_border(group)
    write_log(game.log, f"[#{game.bot.clock}][Initialise] equally distributed troops on the border of our continent {territory_id}")
    return game.move_place_initial_troop(query, territory_id)

def handle_redeem_cards(game: Game, bot_state: BotState, query: QueryRedeemCards) -> MoveRedeemCards:
    """
    After the claiming and placing initial troops phases are over, you can redeem any
    cards you have at the start of each turn, or after killing another player.
    """

    # We will always redeem the minimum number of card sets we can until the 12th card set has been redeemed.
    # This is just an arbitrary choice to try and save our cards for the late game.

    # We always have to redeem enough cards to reduce our card count below five.
    card_sets: list[Tuple[CardModel, CardModel, CardModel]] = []
    cards_remaining = game.state.me.cards.copy()

    while len(cards_remaining) >= 5:
        card_set = game.state.get_card_set(cards_remaining)
        # According to the pigeonhole principle, we should always be able to make a set
        # of cards if we have at least 5 cards.
        assert card_set != None
        card_sets.append(card_set)
        cards_remaining = [card for card in cards_remaining if card not in card_set]

    # Remember we can't redeem any more than the required number of card sets if 
    # we have just eliminated a player.
    if game.state.card_sets_redeemed > 12 and query.cause == "turn_started":
        card_set = game.state.get_card_set(cards_remaining)
        while card_set != None:
            card_sets.append(card_set)
            cards_remaining = [card for card in cards_remaining if card not in card_set]
            card_set = game.state.get_card_set(cards_remaining)

    return game.move_redeem_cards(query, [(x[0].card_id, x[1].card_id, x[2].card_id) for x in card_sets])

def handle_distribute_troops(game: Game, bot_state: BotState, query: QueryDistributeTroops) -> MoveDistributeTroops:
    """
    After you redeem cards (you may have chosen to not redeem any), you need to distribute
    all the troops you have available across your territories. This can happen at the start of
    your turn or after killing another player.
    """
    # initialise
    total_troops = game.state.me.troops_remaining
    distributions = defaultdict(lambda: 0)

    # We need to remember we have to place our matching territory bonus
    # if we have one.
    if len(game.state.me.must_place_territory_bonus) != 0:
        write_log(game.log, f"[#{game.bot.clock}][Distribute] bonus : {game.state.me.must_place_territory_bonus}, my terr : {game.state.get_territories_owned_by(game.state.me.player_id)}")
        assert total_troops >= 2
        for i in game.state.me.must_place_territory_bonus:
            if i in game.state.get_territories_owned_by(game.state.me.player_id):
                distributions[i] += 2
                total_troops -= 2
                break
            
    # step 0
    # game.bot.previous_territories = game.bot.territories[game.bot.id_me]
    game.bot.update_status()
    game.bot.plan_to_do()
    total_troops, distributions = game.bot.distribute_troops_by_plan(total_troops, distributions)
    if total_troops == 0:
        return game.move_distribute_troops(query, distributions)

    # step 1 distribute remain troops in effective border
    # We will distribute troops across our border territories.
    border_territories = game.state.get_all_border_territories(
        game.state.get_territories_owned_by(game.state.me.player_id)
    )

    # We will equally distribute across border territories in the early game,
    # but start doomstacking in the late game.
    if len(game.state.recording) < 4000:
        troops_per_territory = total_troops // len(border_territories)
        leftover_troops = total_troops % len(border_territories)
        for territory in border_territories:
            distributions[territory] += troops_per_territory
    
        # The leftover troops will be put some territory (we don't care)
        distributions[border_territories[0]] += leftover_troops
    
    else:
        my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
        weakest_players = sorted(game.state.players.values(), key=lambda x: sum(
            [game.state.territories[y].troops for y in game.state.get_territories_owned_by(x.player_id)]
        ))

        for player in weakest_players:
            bordering_enemy_territories = set(game.state.get_all_adjacent_territories(my_territories)) & set(game.state.get_territories_owned_by(player.player_id))
            if len(bordering_enemy_territories) > 0:
                print("my territories", [game.state.map.get_vertex_name(x) for x in my_territories])
                print("bordering enemies", [game.state.map.get_vertex_name(x) for x in bordering_enemy_territories])
                print("adjacent to target", [game.state.map.get_vertex_name(x) for x in game.state.map.get_adjacent_to(list(bordering_enemy_territories)[0])])
                selected_territory = list(set(game.state.map.get_adjacent_to(list(bordering_enemy_territories)[0])) & set(my_territories))[0]
                distributions[selected_territory] += total_troops
                break


    return game.move_distribute_troops(query, distributions)

def handle_attack(game: Game, bot_state: BotState, query: QueryAttack) -> Union[MoveAttack, MoveAttackPass]:
    """
    After the troop phase of your turn, you may attack any number of times until you decide to
    stop attacking (by passing). After a successful attack, you may move troops into the conquered
    territory. If you eliminated a player you will get a move to redeem cards and then distribute troops.
    """
    game.bot.update_status()
    game.bot.plan_to_do()
    information = game.bot.attack_by_plan()
    if information is not None:
        attack_territory, target_territory, troops = information
        return game.move_attack(query, attack_territory, target_territory, troops)
    return game.move_attack_pass(query)
    # if game.bot.plan is not None:
    #     src, tgt = game.bot.plan[0]
    #     #if len(src) == len(tgt) == 1 #and got_territory_this_turn:
    #         # return game.move_attack_pass(query)
    #     diff = game.bot.plan[1]
    #     src = sorted(src, key=lambda x:game.state.territories[x].troops)
    #     write_log(game.log, f"[#{game.bot.clock}] start attack from {src} to {tgt}, total diff troops {diff}")
    #     while src and tgt:
    #         # from lowest border
    #         attacker = src.pop(0)
    #         if game.state.territories[attacker].troops == 1:
    #             continue 
    #         adj = game.state.get_all_adjacent_territories([attacker])
    #         tgt_adj = list(set(adj) & set(tgt))
    #         tgt_adj = sorted(tgt_adj, key=lambda x:game.state.territories[x].troops)
    #         write_log(game.log, f"[#{game.bot.clock}] try choose {attacker} to attack, the adj are: {tgt_adj}")
    #         attack_approve = False
    #         while tgt_adj:
    #             # find safe attack territory
    #             taker = tgt_adj.pop(0)
    #             potential_atks = list(set(game.bot.territories[game.bot.id_me]) & set(game.state.get_all_adjacent_territories([taker])))
    #             atk_troops = 0
    #             for atk in potential_atks:
    #                 atk_troops = game.state.territories[atk].troops - 1
    #             taker_troops = game.state.territories[taker].troops
    #             write_log(game.log, f"[#{game.bot.clock}] {attacker} has {atk_troops}, {taker} has {taker_troops}")
    #             if atk_troops - taker_troops < 2:
    #                 write_log(game.log, f"[#{game.bot.clock}] break to choose higher attacker")
    #                 break

    #             # it cannot block all the degree of higher src
    #             block = False
    #             for s in src:
    #                 aaddjj = game.state.get_all_adjacent_territories([s])
    #                 deg = len(set(aaddjj) & set(tgt) - {taker})
    #                 if deg == 0:
    #                     block = True
    #                     break
    #             if not block:
    #                 attack_approve = True
    #                 break
    #         if attack_approve:
    #             return game.move_attack(query, attacker, taker, min(3, game.state.territories[attacker].troops - 1))
    #     return game.move_attack_pass(query)
                

        # attack



    # # We will attack someone.
    # my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    # bordering_territories = game.state.get_all_adjacent_territories(my_territories)

    # def attack_weakest(territories: list[int]) -> Optional[MoveAttack]:
    #     # We will attack the weakest territory from the list.
    #     territories = sorted(territories, key=lambda x: game.state.territories[x].troops)
    #     for candidate_target in territories:
    #         candidate_attackers = sorted(list(set(game.state.map.get_adjacent_to(candidate_target)) & set(my_territories)), key=lambda x: game.state.territories[x].troops, reverse=True)
    #         for candidate_attacker in candidate_attackers:
    #             if game.state.territories[candidate_attacker].troops > 1:
    #                 return game.move_attack(query, candidate_attacker, candidate_target, min(3, game.state.territories[candidate_attacker].troops - 1))


    # if len(game.state.recording) < 4000:
    #     # We will check if anyone attacked us in the last round.
    #     new_records = game.state.recording[game.state.new_records:]
    #     enemy = None
    #     for record in new_records:
    #         match record:
    #             case MoveAttack() as r:
    #                 if r.defending_territory in set(my_territories):
    #                     enemy = r.move_by_player

    #     # If we don't have an enemy yet, or we feel angry, this player will become our enemy.
    #     if enemy != None:
    #         if bot_state.enemy == None or random.random() < 0.05:
    #             bot_state.enemy = enemy
        
    #     # If we have no enemy, we will pick the player with the weakest territory bordering us, and make them our enemy.
    #     else:
    #         weakest_territory = min(bordering_territories, key=lambda x: game.state.territories[x].troops)
    #         bot_state.enemy = game.state.territories[weakest_territory].occupier
            
    #     # We will attack their weakest territory that gives us a favourable battle if possible.
    #     enemy_territories = list(set(bordering_territories) & set(game.state.get_territories_owned_by(enemy)))
    #     move = attack_weakest(enemy_territories)
    #     if move != None:
    #         return move
        
    #     # Otherwise we will attack anyone most of the time.
    #     if random.random() < 0.8:
    #         move = attack_weakest(bordering_territories)
    #         if move != None:
    #             return move

    # # In the late game, we will attack anyone adjacent to our strongest territories (hopefully our doomstack).
    # else:
    #     strongest_territories = sorted(my_territories, key=lambda x: game.state.territories[x].troops, reverse=True)
    #     for territory in strongest_territories:
    #         move = attack_weakest(list(set(game.state.map.get_adjacent_to(territory)) - set(my_territories)))
    #         if move != None:
    #             return move

    # return game.move_attack_pass(query)

def handle_troops_after_attack(game: Game, bot_state: BotState, query: QueryTroopsAfterAttack) -> MoveTroopsAfterAttack:
    """
    After conquering a territory in an attack, you must move troops to the new territory.
    """
    survival_players = 0
    for pid in game.bot.ids_others:
        if game.state.players[pid].alive:
            survival_players += 1
    if survival_players > 3:
        game.bot.got_territoty_this_turn = True
    game.bot.update_status()
    game.bot.plan_to_do()

    # First we need to get the record that describes the attack, and then the move that specifies
    # which territory was the attacking territory.
    record_attack = cast(RecordAttack, game.state.recording[query.record_attack_id])
    move_attack = cast(MoveAttack, game.state.recording[record_attack.move_attack_id])

    moving_troops = game.bot.moving_troops_based_on_plan_code(record_attack, move_attack)
    return game.move_troops_after_attack(query, moving_troops)

    # We will always move the maximum number of troops we can.
    return game.move_troops_after_attack(query, game.state.territories[move_attack.attacking_territory].troops - 1)


def handle_defend(game: Game, bot_state: BotState, query: QueryDefend) -> MoveDefend:
    """
    If you are being attacked by another player, you must choose how many troops to defend with.
    """

    # We will always defend with the most troops that we can.

    # First we need to get the record that describes the attack we are defending against.
    move_attack = cast(MoveAttack, game.state.recording[query.move_attack_id])
    defending_territory = move_attack.defending_territory
    
    # We can only defend with up to 2 troops, and no more than we have stationed on the defending
    # territory.
    defending_troops = min(game.state.territories[defending_territory].troops, 2)
    return game.move_defend(query, defending_troops)


def handle_fortify(game: Game, bot_state: BotState, query: QueryFortify) -> Union[MoveFortify, MoveFortifyPass]:
    """At the end of your turn, after you have finished attacking, you may move a number of troops between
    any two of your territories (they must be adjacent)."""

    game.bot.update_status()
    game.bot.plan_to_do()
    game.bot.got_territoty_this_turn = False
    information = game.bot.fortify_troops()
    if information is not None:
        src, tgt, troops = information
        return game.move_fortify(query, src, tgt, troops)
    return game.move_fortify_pass(query)

    # We will always fortify towards the most powerful player (player with most troops on the map) to defend against them.
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    total_troops_per_player = {}
    for player in game.state.players.values():
        total_troops_per_player[player.player_id] = sum([game.state.territories[x].troops for x in game.state.get_territories_owned_by(player.player_id)])

    most_powerful_player = max(total_troops_per_player.items(), key=lambda x: x[1])[0]

    # If we are the most powerful, we will pass.
    if most_powerful_player == game.state.me.player_id:
        return game.move_fortify_pass(query)
    
    # Otherwise we will find the shortest path between our territory with the most troops
    # and any of the most powerful player's territories and fortify along that path.
    candidate_territories = game.state.get_all_border_territories(my_territories)
    most_troops_territory = max(candidate_territories, key=lambda x: game.state.territories[x].troops)

    # To find the shortest path, we will use a custom function.
    shortest_path = find_shortest_path_from_vertex_to_set(game.state, most_troops_territory, set(game.state.get_territories_owned_by(most_powerful_player)))
    # We will move our troops along this path (we can only move one step, and we have to leave one troop behind).
    # We have to check that we can move any troops though, if we can't then we will pass our turn.
    if len(shortest_path) > 0 and game.state.territories[most_troops_territory].troops > 1:
        return game.move_fortify(query, shortest_path[0], shortest_path[1], game.state.territories[most_troops_territory].troops - 1)
    else:
        return game.move_fortify_pass(query)


if __name__ == "__main__":
    main()