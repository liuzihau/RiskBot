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

VERSION = '11.0.0'
DEBUG = True

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
    "NA": 0.03,
    "AF": 0.01,
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
    3:1,
    4:3,
    5:3
}

# help function
def a_minus_b(a:list, b:list)->list:
    return list(set(a) - set(b))

def a_or_b(a:list, b:list)->list:
    return list(set(a) | set(b))

def a_and_b(a:list, b:list)->list:
    return list(set(a) & set(b))

def write_log(clock, phase, msg):
    if DEBUG:
        print(f"[#{clock}][{phase}] {msg}", flush=True)

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
    
    # Plan related
    def plan_to_do(self):
        """
        plan
                    {
                    'code': 0, 
                    'name': 'NA', 
                    'reward': 5, 
                    'groups': [
                        {'src': [8, 3], 
                        'tgt': [2], 
                        'enemy_troops': 1, 
                        'assign_troops': 0, 
                        'from': 8, 
                        'to': 2
                        }
                        ], 
                    'cost': 2, 
                    'diff': 8, 
                    'my_territories': [8, 3], 
                    'border_territories': [8, 3]
                    }
        """
            
        # aggressive move
        occupy_plan_list = self.occupy_new_continent()
        kill_plan_list = None # self.kill_player() # TODO
        interupt_plan_list = self.interupt_opponunt_continent() #TODO

        if kill_plan_list is not None and occupy_plan_list is not None:
            killing_reward = kill_plan_list[0]['reward'] * 3 - kill_plan_list[0]['cost']
            if occupy_plan_list[0]['diff'] + self.state.me.troops_remaining > 2:
                occupy_reward = occupy_plan_list[0]['reward'] * 3 - occupy_plan_list[0]['cost']
                if killing_reward > occupy_reward and killing_reward > 0:
                    self.plan = kill_plan_list[0]
                    return
                elif occupy_reward >= killing_reward and occupy_reward > 0:
                    self.plan = occupy_plan_list[0]
                    return
            elif killing_reward > 0:
                self.plan = kill_plan_list[0]
                return
        
        elif kill_plan_list is not None:
            killing_reward = kill_plan_list[0]['reward'] * 3 - kill_plan_list[0]['cost']
            if killing_reward > 0:
                self.plan = kill_plan_list[0]
                return

        elif occupy_plan_list is not None:
            if occupy_plan_list[0]['diff'] + self.state.me.troops_remaining > 2:
                self.plan = occupy_plan_list[0]
                return


        # strategic attack for future
        if occupy_plan_list is not None:
            terr_set, border = occupy_plan_list[0]["my_territories"], occupy_plan_list[0]["border_territories"]
            expension_plan = self.choose_territory_minimuize_border(terr_set, border, occupy_plan_list[0]["name"])
            if expension_plan is not None:
                self.plan = expension_plan
                return 
        
        groups = self.get_sorted_connected_group(self.territories[self.id_me])
        largest_group = groups[0]
        if len(largest_group) > 2:
            border = a_and_b(self.border_territories, largest_group)
            expension_plan = self.choose_territory_minimuize_border(largest_group, border)
            if expension_plan is not None:
                self.plan = expension_plan
                return 
        
    
        minimum_attack_list = self.minimum_attack()
        if minimum_attack_list is not None:
            self.plan = minimum_attack_list[0]

        return

    def choose_territory_minimuize_border(self, terr_set, effective_border, name=None):
        if self.got_territoty_this_turn:
            diff_criteria = 3
            border_criteria = -1
        else:
            diff_criteria = 2
            border_criteria = -2
        origin_border = self.state.get_all_border_territories(terr_set)
        plan = {
            'code': 4 if name is not None else 5,
            'name': name,
            'groups':[],
            'my_territories': terr_set,
            'border_territories': effective_border
        }
        for src in effective_border:
            tgts = list(set(self.state.map.get_adjacent_to(src)) - set(self.territories[self.id_me]))
            for tgt in tgts:
                new_border = self.state.get_all_border_territories(terr_set + [tgt])
                border_decrease_count = len(origin_border) - len(new_border)
                cost = self.state.territories[tgt].troops
                diff = self.state.territories[src].troops - cost - 1
                condition1 = diff + self.state.me.troops_remaining > diff_criteria
                condition2 = border_decrease_count > border_criteria
                condition3 = cost == 1 and diff > diff_criteria + 1
                if (condition1 and condition2) or condition3:
                    plan['groups'].append(
                        {
                            "src":[src],
                            "tgt":[tgt],
                            "enemy_troops":cost,
                            "my_troops":self.state.territories[src].troops,
                            'assign_troops': 0,
                            "from":src,
                            "to":tgt,
                            "border_decrease":border_decrease_count
                        }
                    )
        if len(plan['groups']) > 0:
            plan['groups'] = sorted(plan['groups'], key=lambda x:x['my_troops'] - x['enemy_troops'] + x["border_decrease"]*2, reverse=True)
            plan['cost'] = plan['groups'][0]['enemy_troops']
            plan['diff'] = plan['groups'][0]['my_troops'] - plan['groups'][0]['enemy_troops'] - 1
            plan['groups'][0]['assign_troops'] = max(0, (diff_criteria - plan['diff'] + 1))
            return plan
        return

    def get_border_territories_within_group(self, group):
        adjacent_territories = self.state.get_all_adjacent_territories(group)
        combined_group_and_adjacent = a_or_b(group, adjacent_territories)
        my_reachable_territories = a_and_b(self.territories[self.id_me], combined_group_and_adjacent)
        border_territories = []
        for territory in my_reachable_territories:
            adjacent_to_territory = self.state.map.get_adjacent_to(territory)
            adjacent_within_group = a_and_b(group, adjacent_to_territory)
            for adj_territory in adjacent_within_group:
                if self.state.territories[adj_territory].occupier != self.id_me:
                    border_territories.append(territory)
                    break
        return my_reachable_territories, border_territories
    
    def find_good_attack_source_and_target(self, plan):
        K = 1
        assignable_troops = self.state.me.troops_remaining
        if plan['diff'] + assignable_troops < 1:
            return
        distributions = defaultdict(lambda: 0)
        for group in plan['groups']:
            if 'from' in group:
                group.pop('from') 
            if 'to' in group:
                group.pop('to')

            group['enemy_troops'] = self.sum_up_troops(group['tgt'])
            for tgt in group['tgt']:
                sub_set = a_minus_b(group['tgt'], [tgt])
                if len(sub_set) == 0 or len(group_connected_territories(sub_set, self.state)) == 1:
                    cands = a_and_b(group['src'], self.state.map.get_adjacent_to(tgt))
                    if not cands:
                        continue
                    # try inner first
                    inner_cands = a_minus_b(cands, self.border_territories)
                    outer_cands = a_minus_b(cands, inner_cands)
                    if inner_cands:
                        max_cand = max(cands, key=lambda x: self.state.territories[x].troops-distributions[x])
                        attack_troops = self.state.territories[max_cand].troops - distributions[max_cand] - 1
                        diff = attack_troops - group['enemy_troops']
                        if diff < K:
                            assigned_troops = min((K-diff+1), assignable_troops)
                        else:
                            assigned_troops = 0
                        if diff + assigned_troops >= K:
                            if 'assign_troops' not in group:
                                group['assign_troops'] = 0
                            
                            plan['diff'] += assigned_troops
                            group['assign_troops'] += assigned_troops
                            assignable_troops -= assigned_troops
                            distributions[max_cand] += (attack_troops + assigned_troops)
                            group['from'] = max_cand
                            group['to'] = tgt
                            break
                    if outer_cands:
                        max_cand = max(outer_cands, key=lambda x: self.state.territories[x].troops-distributions[x])
                        attack_troops = self.state.territories[max_cand].troops - distributions[max_cand] - 1
                        diff = attack_troops - group['enemy_troops']
                        if diff < K:
                            assigned_troops = min((K-diff), assignable_troops)
                        else:
                            assigned_troops = 0
                        
                        if diff + assigned_troops < K:
                            continue

                        if 'assign_troops' not in group:
                            group['assign_troops'] = 0
                        
                        plan['diff'] += assigned_troops
                        group['assign_troops'] += assigned_troops
                        assignable_troops -= assigned_troops
                        distributions[max_cand] += (attack_troops + assigned_troops)
                        group['from'] = max_cand
                        group['to'] = tgt
                        break
            if 'from' not in group or 'to' not in group:
                return None
        return plan
    
    def occupy_new_continent(self):
        """
        find my border territories in the continent and
        """

        plan_list = []
        for name in CONTINENT:
            plan = {
                "code":0,
                "name":name,
                "reward": REWARD[name],
                "groups":[]
                }
            enemy_territories = a_minus_b(CONTINENT[name], self.territories[self.id_me])
            if len(enemy_territories) == 0:
                continue
            ttl_my_reachable_territories, ttl_border_territories = self.get_border_territories_within_group(enemy_territories)
            if len(ttl_my_reachable_territories) == 0:
                continue
            enemy_troops = self.sum_up_troops(enemy_territories)
            my_troops = self.sum_up_troops(ttl_border_territories)
            cost = enemy_troops + len(enemy_territories) - 1 # the last one doesn't count
            diff = my_troops - cost - len(ttl_border_territories)
            plan['cost'] = cost
            plan['diff'] = diff
            plan['my_territories'] = ttl_my_reachable_territories
            plan['border_territories'] = ttl_border_territories

            enemy_groups = self.get_sorted_connected_group(enemy_territories)
            for enemy_group in enemy_groups:
                my_reachable_territories, border_territories = self.get_border_territories_within_group(enemy_group)
                if len(my_reachable_territories) == 0:
                    break
                plan["groups"].append(
                    {
                        "src":border_territories,
                        "tgt":enemy_group,
                        }
                )
            plan = self.find_good_attack_source_and_target(plan)
            if plan is not None:
                plan_list.append(plan)
        if len(plan_list) > 0:
            plan_list = sorted(plan_list, key=lambda x: x['diff'], reverse=True)
            return plan_list
        return
    
    def kill_player(self):
        if self.plan is not None:
            pid_list = [self.plan["pid"]]
        else:
            pid_list = self.ids_others

        plan_list = []
        reward_weight = self.clock / 500
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
        plan = {
            'code': 2, 
            'name': None, 
            'reward': None,
            'groups': [],
            'my_territories': self.territories[self.id_me], 
            'border_territories': self.border_territories
        }
        for tid in self.border_territories:
            current_territory = self.state.territories[tid]
            candidates = a_minus_b(self.state.map.get_adjacent_to(tid), self.territories[self.id_me])
            for cid in candidates:
                adjacent_territory = self.state.territories[cid]
                cost = adjacent_territory.troops
                diff = current_territory.troops - cost - 1
                if diff + self.state.me.troops_remaining < 2:
                    continue
                # for name in CONTINENT:
                #     if cid in CONTINENT[name]:
                plan['groups'].append(
                    {
                        'src': [tid], 
                        'tgt': [cid], 
                        'enemy_troops': cost,
                        'my_troops': current_territory.troops,
                        'assign_troops': 0, 
                        "from": tid,
                        "to": cid,
                        }
                )
        if len(plan['groups']) > 0:
            plan['groups'] = sorted(plan['groups'], key=lambda x:x['enemy_troops'])
            plan['cost'] = plan['groups'][0]['enemy_troops']
            plan['diff'] = plan['groups'][0]['my_troops'] - plan['groups'][0]['enemy_troops'] - 1
            plan['groups'][0]['assign_troops'] = max(0, (2 - plan['diff'] + 1))
            return 
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
    
    def get_sorted_connected_group(self, territories):
        groups = group_connected_territories(territories, self.state)
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

    def sum_up_troops(self, territoies):
        troops = 0
        for tid in territoies:
            territory = self.state.territories[tid]
            troops += territory.troops
        return troops
    
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
        groups = self.get_sorted_connected_group(self.territories[self.id_me])
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
                        distributions[source] += got_troops
                        total_troops -= got_troops
                        write_log(self.clock, 'Distribute', f"distributed {got_troops} troops to territory {source}")
                    if total_troops == 0:
                        break
            else:
                for group in self.plan['groups']:
                    need_troops = group['assign_troops']
                    distributed_troops = min(total_troops, need_troops)
                    distributions[group["from"]] += distributed_troops
                    total_troops -= distributed_troops
                    write_log(self.clock, 'Distribute', f"distributed {distributed_troops} troops to territory {group['from']}")
        return total_troops, distributions

    def distribute_troops_to_connected_border(self, total_troops, distributions):
        groups = self.get_sorted_connected_group(self.territories[self.id_me])
        borders = self.state.get_all_border_territories(groups[0])
        pq = []
        for border in borders:
            heapq.heappush(pq, (self.state.territories[border].troops, border))
        while total_troops > 0:
            troops, border = heapq.heappop(pq)
            distributions[border] += 1
            heapq.heappush(pq, (troops+1, border))
            total_troops -= 1
            if total_troops == 0:
                break
        return total_troops, distributions
    
    # Attack
    def update_plan(self):
        if self.plan is None:
            return
        
        if self.plan['code'] == 0:
            self.plan = self.find_good_attack_source_and_target(self.plan)
        
        if not self.valid_attack():
            self.plan = None

    def valid_attack(self):
        if self.plan is None:
            return False
        src = self.plan['groups'][0]['from']
        tgt = self.plan['groups'][0]['to']
        if self.state.territories[src].troops > self.state.territories[tgt].troops:
            return True
        return False
    
    def attack_by_plan(self):
        if self.plan:
            return self.plan['groups'][0]['from'], self.plan['groups'][0]['to'], min(3, self.state.territories[self.plan['groups'][0]['from']].troops - 1)

    
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
            write_log(self.clock, "AfterAttack", f"move from {src_territory} to {tgt_territory} with moving_troops")
            return max_troops - 1
        elif self.plan["code"] == 2:
            return self.put_troops_on_border(src_territory, tgt_territory, max_troops, min_troops)
        else:
            return self.put_troops_on_border(src_territory, tgt_territory, max_troops, min_troops)


    def put_troops_on_border(self, src, tgt, max_troops, min_troops):
        if src in self.border_territories and tgt in self.border_territories:
            write_log(self.clock, "AfterAttack", f"{src} and {tgt} both are border, equally put troops {max(max_troops // 2, min_troops)}")
            return max(max_troops // 2, min_troops)
        elif tgt in self.border_territories:
            write_log(self.clock, "AfterAttack", f"only {tgt} is border, moving all troops {max_troops - 1}")
            return max_troops - 1
        elif src in self.border_territories:
            write_log(self.clock, "AfterAttack", f"only {src} is border, moving min troops {min_troops}")
            return min_troops
        else:
            write_log(self.clock, "AfterAttack", f"both {src} and {tgt} are not border, moving all troops {max_troops - 1}")
            return max_troops - 1
        
    def put_troops_on_attack_territory(self, src, tgt, max_troops, min_troops):
        if self.plan is None:
            return self.put_troops_on_border(src, tgt, max_troops, min_troops)
        potential_border = []
        my_terr_plus_continent = a_or_b(CONTINENT[self.plan["name"]], self.territories[self.id_me])
        groups = self.get_sorted_connected_group(my_terr_plus_continent)
        for group in groups:
            if len(a_and_b(group, CONTINENT[self.plan["name"]])) == len(CONTINENT[self.plan["name"]]):
                potential_border = self.state.get_all_border_territories(group)
                break

        if src in potential_border:
            enemy_group = a_minus_b(self.plan['groups'][0]['tgt'], [tgt])
            friend_group = a_minus_b(self.plan['groups'][0]['src'], [src])
            friend_borders = []
            for g in enemy_group:
                adj = a_and_b(self.state.map.get_adjacent_to(g), friend_group)
                friend_borders = a_and_b(friend_borders, adj)
            friend_troops = self.sum_up_troops(friend_borders)
            effective_troops = (friend_troops - len(friend_group)) // 2
            idle_troops = max_troops - self.sum_up_troops(enemy_group) - len(enemy_group) + effective_troops
            ideal_defend_troops = max(1, idle_troops // len(potential_border))
            final_troops = max(min_troops, max_troops - ideal_defend_troops)
            write_log(self.clock, "AfterAttack", f"trying occupy {self.plan['name']}, and {src} is door, put {max_troops - final_troops} for protecting")
            return final_troops
        else:
            write_log(self.clock, "AfterAttack", f"trying occupy {self.plan['name']}, and {src} is not door, put 1 (potential border:{potential_border})")
            return max_troops - 1

    # Fortify
    def fortify_troops(self):
        tgts, group = self.find_weakest_territories()
        srcs = self.find_strongest_territories(tgts, group)
        if len(srcs) == 0:
            return 
        new_tgts = [tgt for tgt in tgts if self.state.territories[tgt].troops == self.state.territories[tgts[0]].troops][:3]
        new_srcs = srcs[:3]

        moving_plan = []
        for src, moving_troops in new_srcs:
            for tgt in new_tgts:
                if src is not None and src != tgt:
                    path = find_shortest_path_from_vertex_to_vertex_via_group(self.state, src, tgt, group)
                    if len(path) == 2:
                        write_log(self.clock, "Fortify", f"move {moving_troops} troops from {src} to {path[1]}(target :{tgt}) within our territories group {group} (our territoreis={self.territories[self.id_me]})")
                        return path[0], path[1], moving_troops
                    moving_plan.append(
                        (len(path), path, moving_troops)
                    )

        if len(moving_plan) != 0:
            ans = min(moving_plan, key=lambda x:(x[0], -1*x[2]))
            write_log(self.clock, "Fortify", f"move {moving_troops} troops from {ans[1][0]} to {ans[1][1]}(target :{ans[1][-1]}) within our territories group {group} (our territoreis={self.territories[self.id_me]})")
            return ans[1][0], ans[1][1], ans[2]
        
    
    def find_weakest_territories(self):
        # check if we hold continent
        # find the group wtih continent and find the minimum border for the target
        # If we don't have continent, just choose the minimum border within the biggest group
        reward_pairs = sorted(REWARD.items(), key=lambda x:x[1], reverse=True)
        groups = self.get_sorted_connected_group(self.territories[self.id_me])

        for name, reward in reward_pairs:
            if set(CONTINENT[name]) & set(self.territories[self.id_me]) != set(CONTINENT[name]):
                continue
            for group in groups:
                if set(CONTINENT[name]) & set(group) != set(CONTINENT[name]):
                    continue
                borders = a_and_b(group, self.border_territories)
                write_log(self.clock, "Fortify", f"find weakest border from {borders} in {group} (our territoreis={self.state.get_territories_owned_by(self.id_me)})")
                return sorted(borders, key=lambda x: self.state.territories[x].troops), group

        borders = list(set(groups[0]) & set(self.border_territories))
        return sorted(borders, key=lambda x: self.state.territories[x].troops), groups[0]
    
    def find_strongest_territories(self, weakest_territories, group):
        # first we check the largest troops we can use in the inner territories
        # second we check the maximum trrops we can use in the border territories
        # if split half the border the troops still safe and larger than inner troops than use border
        # use inner
        weakest_troops = self.state.territories[weakest_territories[0]].troops

        inner_territories = list(set(group) - set(self.border_territories))
        if inner_territories:
            cands = [(t, self.state.territories[t].troops - 1) for t in inner_territories if self.state.territories[t].troops > 2]
            cands = sorted(cands, key=lambda x:x[1], reverse=True)[:3]
        else:
            cands = []

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
            if final_moving > 3:
                cands.append((border_territory, final_moving))
        return cands

        
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
    write_log("-1","Version", f"{VERSION}")

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
        write_log(game.bot.clock, "Claim", f"decided by block, {territory}")
        return game.move_claim_territory(query, territory)

    # step 2 check if we can dominent one specific continent
    territories = game.bot.search_preferred_continent()
    if territories:
        territory = game.bot.choose_adjacent_with_info(territories)
        write_log(game.bot.clock, "Claim", f"decided by collect continent, {territory}")
        return game.move_claim_territory(query, territory)
    
    # step 3 try to maximise the adjacent territory
    sorted_group = game.bot.get_sorted_connected_group(game.bot.territories[game.bot.id_me])
    territory = game.bot.try_to_connect_territory_no_gap(sorted_group)
    if territory:
        write_log(game.bot.clock, "Claim", f"decided by connect with possible largest territories, {territory}")
        return game.move_claim_territory(query, territory)
    
    territory = game.bot.try_to_connect_territory_1_gap(sorted_group)
    if territory:
        write_log(game.bot.clock, "Claim", f"decided by 1 gap with possible largest territories, {territory}")
        return game.move_claim_territory(query, territory)
    
    # step 4 pick by degree
    territory = game.bot.pick_by_degree()
    write_log(game.bot.clock, "Claim", f"decided by degree, {territory}")
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
        write_log(game.bot.clock, "Initialise", f"equally distributed troops on the border of our continent {territory_id}")
        return game.move_place_initial_troop(query, territory_id)

    # senario 2: we have edge in a continent
    group = game.bot.check_our_dominent_continent()
    territory_id = game.bot.put_troops_equally_on_border(group)
    write_log(game.bot.clock, "Initialise", f"equally distributed troops on the border of our continent {territory_id}")
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
        write_log(game.bot.clock, "Distribute", f"bonus : {game.state.me.must_place_territory_bonus}, my terr : {game.state.get_territories_owned_by(game.state.me.player_id)}")
        assert total_troops >= 2
        for i in game.state.me.must_place_territory_bonus:
            if i in game.state.get_territories_owned_by(game.state.me.player_id):
                distributions[i] += 2
                total_troops -= 2
                break
            
    # step 0
    # game.bot.previous_territories = game.bot.territories[game.bot.id_me]
    game.bot.update_status()
    game.bot.plan = None
    game.bot.plan_to_do()
    write_log(game.bot.clock, "Distribute", f"follow plan {game.bot.plan}")
    total_troops, distributions = game.bot.distribute_troops_by_plan(total_troops, distributions)
    if total_troops == 0:
        return game.move_distribute_troops(query, distributions)

    # step 1 distribute remain troops in effective border
    # We will distribute troops across our border territories.
    # We will equally distribute across border territories in the early game,
    # but start doomstacking in the late game.
    if len(game.state.recording) < 4000:
        total_troops, distributions = game.bot.distribute_troops_to_connected_border(total_troops, distributions)
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
    last_record = cast(RecordAttack, game.state.recording)[-1]
    if last_record.record_type == 'move_troops_after_attack':
        game.bot.plan = None
        game.bot.plan_to_do()
    elif last_record.record_type != 'move_distribute_troops':
        game.bot.update_plan()
        if game.bot.plan is None and not game.bot.got_territoty_this_turn:
            game.bot.plan_to_do()
    write_log(game.bot.clock, 'Attack', f"plan: {game.bot.plan}")
    information = game.bot.attack_by_plan()
    if information is not None:
        attack_territory, target_territory, troops = information
        return game.move_attack(query, attack_territory, target_territory, troops)
    return game.move_attack_pass(query)
   

def handle_troops_after_attack(game: Game, bot_state: BotState, query: QueryTroopsAfterAttack) -> MoveTroopsAfterAttack:
    """
    After conquering a territory in an attack, you must move troops to the new territory.
    """

    survival_players = 0
    for pid in game.bot.ids_others:
        if game.state.players[pid].alive:
            survival_players += 1
    if survival_players > 3 or game.bot.clock < 3000:
        game.bot.got_territoty_this_turn = True
    game.bot.update_status()
    record_attack = cast(RecordAttack, game.state.recording[query.record_attack_id])
    # if game.bot.clock > 2000:
    #     for pid in range(5):
    #         print(game.state.players[pid], flush=True)
    #     for record in game.state.recording:
    #         if record.record_type == 'move_redeem_cards':
    #             print(record, flush=True)
    #     raise


    move_attack = cast(MoveAttack, game.state.recording[record_attack.move_attack_id])
    moving_troops = game.bot.moving_troops_based_on_plan_code(record_attack, move_attack)
    return game.move_troops_after_attack(query, moving_troops)

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
    game.bot.got_territoty_this_turn = False
    information = game.bot.fortify_troops()
    if information is not None:
        src, tgt, troops = information
        return game.move_fortify(query, src, tgt, troops)
    return game.move_fortify_pass(query)



if __name__ == "__main__":
    main()