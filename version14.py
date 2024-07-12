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

VERSION = '14.0.4'
DEBUG = True

WHOLEMAP = [i for i in range(42)]

CONTINENT = {
    "AU": [38, 39, 41, 40],
    "SA": [28, 31, 29, 30],
    "AF": [35, 37, 32, 33, 36, 34],
    "EU": [12, 10, 9, 15, 13, 14, 11],
    "NA": [2, 3, 8, 7, 6, 1, 4, 5, 0],
    "AS": [20, 27, 21, 25, 26, 19, 23, 17, 24, 18, 22, 16]
    }
SECONDCONTINENT = {
    "AU":["AS"],
    "SA":["AF", "NA"],
    "AF":["EU", "SA"],
    "EU":["AF", "NA"],
    "NA":["AF", "EU"],
    "AS":["AU", "NA", "AF", "EU"]
}

PREFER = {
    "AU": 0.02,
    "SA": 0.03,
    "NA": 0.01,
    "AF": 0.02,
    "EU": 0.0,
    "AS": -0.5
    }

DOOR = {
    "AU": [40],
    "SA": [29, 30],
    "NA": [4, 0, 2],
    "AF": [33, 36, 34],
    "EU": [10, 15, 13, 14],
    "AS": [21, 26, 24, 22, 16]
}
DEVIATION = {
    "AU": 1,
    "SA": 1,
    "NA": 2,
    "AF": 2,
    "EU": 3,
    "AS": 3
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
def defend_coefficient(enemy_troops):
    if 0 < enemy_troops < 3:
        return 1
    elif enemy_troops < 6:
        return 0
    elif enemy_troops < 10:
        return -int(enemy_troops * .25)
    else:
        return -int(enemy_troops * .35)
    
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

def heap_helper(pq, total_troops, distributions):
    k = max(1, total_troops // 8)
    record = defaultdict(lambda: 0)
    while total_troops > 0:
        troops, gid = heapq.heappop(pq)
        assign = min(total_troops, k)
        distributions[gid] += assign
        record[gid] += assign
        heapq.heappush(pq, (troops + assign, gid))
        total_troops -= assign
        if total_troops == 0:
            return total_troops, distributions, record
    return total_troops, distributions, record

class BotState:
    def __init__(self, state):
        self.state = state
        self.id_me = None
        self.id_all_player = []
        self.ids_others = []
        self.territories = {}
        self.troops = {}
        self.economy = {}
        self.continent_owner = {}
        self.continent_owned_by = {}
        self.threat_this_turn = {}
        self.troops_for_defend = 0
        self.adjacent_territories = []
        self.border_territories = []
        self.plan = None
        self.got_territoty_this_turn = False
        self.clock = 0
    
    # help function
    def construct_player_id(self):
        if self.id_me is None:
            self.id_me = self.state.me.player_id
            self.id_all_player = [player for player in self.state.players]
            self.ids_others = a_minus_b(self.id_all_player, [self.id_me])

    def check_continent_owner(self, pid):
        self.continent_owned_by[pid] = []
        for name in CONTINENT:
            self.continent_owner[name] = None
            intersection = a_and_b(CONTINENT[name], self.territories[pid])
            if len(intersection) == len(CONTINENT[name]):
                self.continent_owner[name] = pid
                self.continent_owned_by[pid].append(name)
    
    def get_overall_player_status(self):
        for pid in self.id_all_player + [None]:
            self.territories[pid] = self.state.get_territories_owned_by(pid)
            self.check_continent_owner(pid)
            self.troops[pid] = self.sum_up_troops(self.territories[pid])
            if pid is not None:
                self.economy[pid] = self.sum_up_troops_get_next_turn(pid) 
    
    def approve_infinity_fire(self):
        return self.troops[self.id_me] / sum(self.troops.values()) > 0.28 and (self.clock > 1000 or len(self.continent_owned_by[self.id_me])>1)
    
    def update_status(self):
        self.construct_player_id()
        self.get_overall_player_status()
        self.adjacent_territories = self.state.get_all_adjacent_territories(self.territories[self.id_me])
        self.border_territories = self.state.get_all_border_territories(self.territories[self.id_me])
    
    def write_player_information(self, pid):
        card_count = len(self.state.me.cards) if pid == self.id_me else self.state.players[pid].card_count
        msg = f"cards: {card_count} troops: {self.troops[pid]}, economy: {self.economy[pid]}, hold continents:{self.continent_owned_by[pid]}, territories: {self.territories[pid]}"
        write_log(self.clock, f"Status Player{pid}", msg)
    
    def troops_can_distribute(self):
        return max(self.state.me.troops_remaining - self.troops_for_defend, 0)

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
    
    def get_group_contain_sub_group_from_groups(self, groups, sub_group):
        for group in groups:
            if len(a_and_b(group, sub_group)) == len(sub_group):
                return group
            
    def get_threat_list_from_group(self, group):
        effective_borders = a_and_b(self.border_territories, group)
        for eff_border in effective_borders:
            if eff_border in self.threat_this_turn:
                continue
            adj_list = self.state.map.get_adjacent_to(eff_border)
            adj_list = a_minus_b(adj_list, self.territories[self.id_me])
            tid_with_maximum_troops = max(adj_list, key= lambda x: self.state.territories[x].troops)
            enemy_troops = self.state.territories[tid_with_maximum_troops].troops
            self.threat_this_turn[eff_border] = {
                    "my_troops": self.state.territories[eff_border].troops,
                    "enemy_troops": enemy_troops,
                    "diff": self.state.territories[eff_border].troops - enemy_troops,
                    "is_door": False,
                    "currently_hold": True
                    }
    
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

        # step 0 check if last run is killing player, if so, keep killing
        tried_kill = False
        if self.plan is not None and self.plan['code'] == 3:
            kill_plan_list = self.kill_player(self.plan['pid'])
            tried_kill = True
            if kill_plan_list is not None:
                self.plan = kill_plan_list[0]
                return
        
        # step 1 reset plan
        self.plan = None
        self.troops_for_defend = 0

        # step 2 try kill player 
        kill_plan_list = None if self.state.card_sets_redeemed < 3 or tried_kill else self.kill_player()
        if kill_plan_list is not None:
            self.plan = kill_plan_list[0]
            return

        # step 3 defend our own continent
        self.get_defending_continent_proposal()
        self.update_defending_troops()
        write_log(self.clock, 'Defend', f"require {self.troops_for_defend} to defend ({self.threat_this_turn})")

        # step 4 try occupy continent
        occupy_plan_list = self.occupy_new_continent()
        write_log(self.clock, 'Occupy debug', f"{occupy_plan_list}")
        if occupy_plan_list is not None:
            if occupy_plan_list[0]['diff'] - occupy_plan_list[0]['defend_difficulty'] > 0:
                for d, v in occupy_plan_list[0]['proposal_threat'].items():
                    if d in self.threat_this_turn:
                        continue
                    self.threat_this_turn[d] = {
                        'my_troops': 0,
                        'enemy_troops': v,
                        'diff': -v,
                        "is_door": True,
                        "currently_hold": False
                    }
                self.plan = occupy_plan_list[0]
                return

        # step 5 try interupt other players' continent
        interupt_plan_list = self.interupt_opponunt_continent() #TODO

        # step 6 try attack 1 territory that in the interested continent 
        if occupy_plan_list is not None:
            terr_set, border = occupy_plan_list[0]["my_territories"], occupy_plan_list[0]["border_territories"]
            expension_plan = self.choose_territory_minimuize_border(terr_set, border, occupy_plan_list[0]["name"])
            if expension_plan is not None:
                self.plan = expension_plan
                return 
        
        # step 7 try attack 1 territory that can cease our border presure or at least the same level
        groups = self.get_sorted_connected_group(self.territories[self.id_me])
        largest_group = groups[0]
        if len(largest_group) > 2:
            border = a_and_b(self.border_territories, largest_group)
            expension_plan = self.choose_territory_minimuize_border(largest_group, border)
            if expension_plan is not None:
                self.plan = expension_plan
                return 
        
        # step 8 find a minimum cost territory to finish at least 1 attack
        minimum_attack_plan = self.minimum_attack()
        if minimum_attack_plan is not None:
            self.plan = minimum_attack_plan

        return

    def get_defending_continent_proposal(self):
        self.threat_this_turn = {}
        continents = self.continent_owned_by[self.id_me]
        groups = self.get_sorted_connected_group(self.territories[self.id_me])
        for name in continents:
            group = self.get_group_contain_sub_group_from_groups(groups, CONTINENT[name])
            if not group:
                write_log(self.clock, 'Defend', f"try find a group contain {name} but fail")
            self.get_threat_list_from_group(group)
        for name in continents:
            for key in self.threat_this_turn:
                if key in DOOR[name]:
                    self.threat_this_turn[key]['is_door'] = True

    def update_defending_troops(self):
        for key in self.threat_this_turn:
            border = self.threat_this_turn[key]
            if border['is_door']:
                final_defend_coeff = defend_coefficient(border['enemy_troops']) + 1
            else:
                final_defend_coeff = defend_coefficient(border['enemy_troops'])
            self.troops_for_defend += max(0, final_defend_coeff - border['diff'])

    def occupy_new_continent(self):
        if len(self.continent_owned_by[self.id_me]) == 1:
            name = self.continent_owned_by[self.id_me][0]
            candidates = SECONDCONTINENT[name]
        else:
            candidates = CONTINENT
        plan_list = []
        for name in candidates:
            if self.continent_owner[name] == self.id_me:
                continue
            enemy_territories = a_minus_b(CONTINENT[name], self.territories[self.id_me])
            ttl_my_reachable_territories, ttl_border_territories = self.get_border_territories_within_group(enemy_territories)
            if len(ttl_my_reachable_territories) == 0:
                continue
            enemy_troops = self.sum_up_troops(enemy_territories)
            my_troops = self.sum_up_troops(ttl_border_territories)
            cost = enemy_troops + len(enemy_territories) - 1 # the last one doesn't count
            diff = my_troops - cost - len(ttl_border_territories)
            defend_difficulty = 0
            proposal_threat = {}
            for d in DOOR[name]:
                adj = self.state.map.get_adjacent_to(d)
                adj = a_minus_b(adj, a_or_b(self.territories[self.id_me], CONTINENT[name]))
                if len(adj) == 0:
                    proposal_threat[d] = 0
                    continue
                theat_id = max(adj, key=lambda x:self.state.territories[x].troops)
                proposal_threat[d] = self.state.territories[theat_id].troops
                effect_difficulty = proposal_threat[d] - defend_coefficient(proposal_threat[d])
                if d in self.territories[self.id_me] and d not in ttl_border_territories:
                    defend_difficulty += max(0, effect_difficulty - self.state.territories[d].troops)
                else:
                    defend_difficulty += effect_difficulty
            if diff + self.troops_can_distribute() < DEVIATION[name]:
                continue
            plan = {
                "code": 0,
                "name": name,
                "reward": REWARD[name],
                "groups": [],
                "cost": cost,
                "diff": diff,
                "defend_difficulty": defend_difficulty,
                "my_territories": ttl_my_reachable_territories,
                "border_territories": ttl_border_territories,
                "proposal_threat": proposal_threat
                }
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
            plan_list = sorted(plan_list, key=lambda x: x['diff'] - x['defend_difficulty'], reverse=True)
            return plan_list
        return
    
    def choose_territory_minimuize_border(self, terr_set, effective_border, name=None):
        if not self.approve_infinity_fire() and self.got_territoty_this_turn:
            return
        if name is None:
            diff_criteria = 2 + int(self.got_territoty_this_turn)
            cost_criteria = self.troops[self.id_me] // 7 - int(self.got_territoty_this_turn)
            border_criteria = -2 + int(self.got_territoty_this_turn)
        else:
            diff_criteria = 2 + int(self.got_territoty_this_turn)
            cost_criteria = 9999
            border_criteria = -4 + int(self.got_territoty_this_turn)
        origin_border = self.state.get_all_border_territories(terr_set)
        plan = {
            'code': 4 if name is not None else 5,
            'name': name,
            'groups':[],
            'my_territories': terr_set,
            'border_territories': effective_border
        }
        for src in effective_border:
            tgts = a_minus_b(self.state.map.get_adjacent_to(src), self.territories[self.id_me])
            if name is not None:
                tgts = a_and_b(tgts, CONTINENT[name])
            for tgt in tgts:
                new_border = self.state.get_all_border_territories(terr_set + [tgt])
                border_decrease_count = len(origin_border) - len(new_border)
                cost = self.state.territories[tgt].troops
                diff = self.state.territories[src].troops - cost - 1
                condition1 = diff + self.troops_can_distribute() > diff_criteria
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

    def find_good_attack_source_and_target(self, plan):
        K = 1
        assignable_troops = self.troops_can_distribute()
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
                            group['my_troops'] = self.state.territories[max_cand].troops
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
                        group['my_troops'] = self.state.territories[max_cand].troops
                        group['from'] = max_cand
                        group['to'] = tgt
                        break
            if 'from' not in group or 'to' not in group:
                return None
        return plan
    
    def kill_player(self, target=None):
        target_list = [target] if target is not None else self.ids_others
        plan_list = []
        my_troops = self.sum_up_troops(self.border_territories) - len(self.border_territories)
        for pid in target_list:
            if not self.state.players[pid].alive:
                continue
            enemy_troops = self.sum_up_troops(self.territories[pid])# - len(self.border_territories)
            troops_edge = my_troops - enemy_troops - len(self.territories[pid])
            write_log(self.clock, 'Kill Overview', f"[Player {pid}] card_redeemed: {self.state.card_sets_redeemed}, enemy_hand_card: {self.state.players[pid].card_count}, enemy_troops: {enemy_troops}, enemy_territories: {len(self.territories[pid])}, my_troops: {my_troops}")
            if troops_edge < 5:
                continue
            plan = {
                'code':3, 
                'name':None,
                'pid': pid,
                'reward': (self.state.card_sets_redeemed - 3) * self.state.players[pid].card_count * 1.5,
                'groups':[],
                'my_territories': self.territories[self.id_me], 
                'border_territories': self.border_territories
            }
            if self.state.players[pid].card_count < 2:
                continue

            groups = self.find_killing_path(pid)
            if groups is not None:
                groups = sorted(groups, key=lambda x: x['enemy_troops'], reverse=True)
                while groups[0]['from'] not in self.territories[self.id_me]:
                    groups.append(groups.pop(0))
                plan['groups'] = groups
                total_cost = 0
                total_diff = 0
                for group_plan in plan['groups']:
                    total_cost += group_plan["enemy_troops"]
                    total_diff += group_plan["my_troops"] - group_plan["enemy_troops"] + len(group_plan["tgt"]) + len(group_plan['target'])
                plan['cost'] = total_cost
                plan['diff'] = total_diff
                if total_diff > 2:
                    plan_list.append(plan)
            
        if len(plan_list) > 0:
            plan_list = sorted(plan_list, key=lambda x:x['diff'], reverse=True)
            return plan_list
        
    def find_killing_path(self, target_id):
        enemy_territories = a_minus_b(WHOLEMAP, self.territories[self.id_me])
        target_groups = group_connected_territories(self.territories[target_id], self.state)
        return self.find_shortest_cost_from_group_to_group(self.border_territories, target_groups, enemy_territories)

    def find_shortest_cost_from_group_to_group(self, srcs: list, targets: list, enemy_territories) -> Union[list[int], None]:
        criteria = 3
        groups = []
        assignable_troops = self.troops_can_distribute()
        allocated_troops = defaultdict(lambda: 0)
        while len(targets) > 0:
            paths = []
            for src in srcs:
                path, troops_diff, target = self.dijkstra(src, targets, enemy_territories, allocated_troops)
                if path is None:
                    continue
                paths.append(
                    {
                        'src':[path[0]],
                        "tgt":path[1:],
                        "enemy_troops": troops_diff + (self.state.territories[src].troops - allocated_troops[src] - 1),
                        "my_troops":self.state.territories[src].troops,
                        "from": path[0],
                        "to": path[1],
                        "target":target
                                }
                )
            chosen_paths = sorted(paths, key=lambda x:(len(x['tgt']), x['enemy_troops'] - x['my_troops']))
            chosen_path = None
            while len(chosen_paths) > 0:
                cand = chosen_paths.pop(0)
                for tid in a_minus_b(cand['target'], [cand['to']]):
                    cand["enemy_troops"] += self.state.territories[tid].troops
                my_active_troops = assignable_troops + cand['my_troops'] - allocated_troops[cand['from']] - 1
                minimum_needed_troops = cand['enemy_troops'] + len(cand['tgt'])
                if my_active_troops - minimum_needed_troops > criteria:
                    chosen_path = cand
                    break
            if chosen_path is None:
                groups = None
                break

            write_log(self.clock, 'Debug Kill', f"chosen path for {chosen_path['target']}, {chosen_path}")
            
            chosen_path['assign_troops'] = max(0, (criteria + minimum_needed_troops + 1 - chosen_path['my_troops']))
            allocated_troops[chosen_path['from']] += minimum_needed_troops + criteria
            assignable_troops -= chosen_path['assign_troops']
            groups.append(chosen_path)

            targets.remove(chosen_path['target'])
            new_added_terrs = a_or_b(chosen_path["src"] + chosen_path["tgt"], chosen_path['target'])
            srcs = a_or_b(srcs, new_added_terrs)
            enemy_territories = a_minus_b(enemy_territories, srcs)
            srcs = self.state.get_all_adjacent_territories(enemy_territories)

        write_log(self.clock, 'Debug Kill', f"final group {groups}")
        return groups
        
    def dijkstra(self, src: int, targets: list, enemy_territories, allocated_troops) -> tuple:
        # Initialize the priority queue
        pq = []
        distances = {vertex: float('infinity') for vertex in enemy_territories}
        previous_vertices = {src:None}

        # Set the distance for start vertices
        start_troops = self.state.territories[src].troops if src in self.territories[self.id_me] else 0
        distances[src] = -(start_troops - allocated_troops[src] - 1)
        heapq.heappush(pq, (-(start_troops - allocated_troops[src] - 1), src))

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
            neighbors = a_and_b(self.state.map.get_adjacent_to(current_vertex), enemy_territories)

            for neighbor in neighbors:
                distance = current_distance + self.state.territories[neighbor].troops
                # Only consider this new path if it's better
                if distance < distances[neighbor]:
                    distances[neighbor] = distance
                    previous_vertices[neighbor] = current_vertex
                    heapq.heappush(pq, (distance, neighbor))

        return None, float('infinity'), None
    
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
                if diff + self.troops_can_distribute() < 0:
                    continue
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
            return plan
        return 

    # Claim Territories
    def choose_adjacent_with_info(self, name):
        for territory in CONTINENT[name]:
            if territory in self.territories[None] and territory in self.adjacent_territories:
                return territory
        for territory in CONTINENT[name]:
            if territory in self.territories[None]:
                return territory
    
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
                return prefered_name
        return None
    
    def check_continent_availibility(self):
        pr_list = []
        for name in ['AU', 'SA', 'AF', 'NA', 'EU']:
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
    
    def sum_up_troops_get_next_turn(self, pid):
        basic_income = max(3, len(self.territories[pid]) // 3)
        bonus_income = 0 # TODO I don't know what it is
        continent_income = 0
        for name in self.continent_owned_by[pid]:
            continent_income = REWARD[name]
        
        return basic_income + bonus_income + continent_income 
    
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
            for group in self.plan['groups']:
                if group['assign_troops'] == 0:
                    continue
                assign_troops = group['assign_troops']
                if group['from'] not in self.territories[self.id_me]:
                    while group['from'] not in self.territories[self.id_me]:
                        for g in self.plan["groups"]:
                            if group['from'] in g['tgt']+g['target']:
                                group = g
                distributed_troops = min(total_troops, assign_troops)
                distributions[group["from"]] += distributed_troops
                total_troops -= distributed_troops
                write_log(self.clock, 'Distribute', f"distributed {distributed_troops} troops to territory {group['from']} by plan code {self.plan['code']}")

            if self.plan['code'] == 3 and total_troops > 0:
                pq = []
                for group in self.plan['groups']:
                    if group['from'] not in self.territories[self.id_me]:
                        while group['from'] not in self.territories[self.id_me]:
                            for g in self.plan["groups"]:
                                if group['from'] in g['tgt']+g['target']:
                                    group = g
                    heapq.heappush(pq, (group['my_troops'], group['from']))
                total_troops, distributions, record = heap_helper(pq, total_troops, distributions)
                write_log(self.clock, 'Distribute', f"extra distribute for code 3: {dict(record)}")

            elif self.plan['code'] == 0 and total_troops > 0:
                total_troops, distributions = self.stack_to_attack_point(total_troops, distributions)
        
        total_troops, distributions = self.distribute_troops_by_defending(total_troops, distributions)
        if total_troops > 0:
            total_troops, distributions = self.distribute_troops_to_connected_border(total_troops, distributions)

        return total_troops, distributions

    def distribute_troops_by_defending(self, total_troops, distributions):
        if len(self.threat_this_turn) == 0:
            return total_troops, distributions
        pq = []
        for border, values in self.threat_this_turn.items():
            if not values['currently_hold']:
                continue
            if values['is_door']:
                heapq.heappush(pq, (values['diff'] - 2, border))
            else:
                heapq.heappush(pq, (values['diff'], border))
        if len(pq) == 0:
            return total_troops, distributions
        total_troops, distributions, record = heap_helper(pq, total_troops, distributions)
        write_log(self.clock, 'Distribute', f"defending continent: {dict(record)}")
        return total_troops, distributions

    def distribute_troops_to_connected_border(self, total_troops, distributions):
        if total_troops == 0:
            return total_troops, distributions
        groups = self.get_sorted_connected_group(self.territories[self.id_me])
        borders = self.state.get_all_border_territories(groups[0])
        pq = []
        for border in borders:
            heapq.heappush(pq, (self.state.territories[border].troops, border))
        total_troops, distributions, record = heap_helper(pq, total_troops, distributions)
        write_log(self.clock, 'Distribute', f"put in connected border: {dict(record)}")
        return total_troops, distributions
    
    def stack_to_attack_point(self, total_troops, distributions):
        if self.plan is not None:
            group_counts = len(self.plan['groups'])
            equally_distribute = total_troops // group_counts
            if equally_distribute > 0:
                for group in self.plan['groups']:
                    if group['from'] not in self.territories[self.id_me]:
                        while group['from'] not in self.territories[self.id_me]:
                            for g in self.plan["groups"]:
                                if group['from'] in g['tgt']+g['target']:
                                    group = g
                    distributions[group['from']] += equally_distribute
                    total_troops -= equally_distribute
                    write_log(self.clock, 'Distribute', f"extra distributed {equally_distribute} troops to territory {group['from']} for the attack_point by plan code {self.plan['code']}")

            distributions[self.plan['groups'][0]['from']] += total_troops
            write_log(self.clock, 'Distribute', f"extra distributed {total_troops} troops to territory {self.plan['groups'][0]['from']} for the attack_point by plan code {self.plan['code']}")
            total_troops -= total_troops

        else:
            total_troops, distributions =  self.distribute_troops_to_connected_border(total_troops, distributions)

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
        elif self.plan["code"] == 3:
            return self.put_troops_on_target_greedy(src_territory, tgt_territory, max_troops, min_troops)
        elif self.plan["code"] in [2, 4, 5]:
            return self.put_troops_on_attack_territory(src_territory, tgt_territory, max_troops, min_troops)
        else:
            return self.put_troops_on_border(src_territory, tgt_territory, max_troops, min_troops)

    def put_troops_on_target_greedy(self, src, tgt, max_troops, min_troops):
        target_enemy = 0
        other_enemy = 0
        for group in self.plan['groups']:
            if group['from'] == src and group['to'] == tgt:
                enemy_territories = a_minus_b(group['tgt'], [tgt]) + group['target']
                target_enemy += self.sum_up_troops(enemy_territories) + len(enemy_territories) - 1
            elif group['from'] == src:
                enemy_territories = group['tgt'] + group['target']
                other_enemy += self.sum_up_troops(enemy_territories) + len(enemy_territories) - 1

        if other_enemy == 0:
            write_log(self.clock, "AfterAttack", f"no sharing src with other attack plan move all troops {max_troops - 1}")
            return max_troops - 1
        idle_troops = max_troops - target_enemy - other_enemy - 1
        ratio = target_enemy / (target_enemy + other_enemy)
        smothing_ratio = ratio * (2/3) + 0.5 * (1/3)
        portion_troops = int(idle_troops * smothing_ratio)
        if idle_troops > 0:
            write_log(self.clock, "AfterAttack", f"sharing src with other attack plan with extra {idle_troops} troops, moving {max(min_troops, target_enemy + idle_troops // 2 - 1)}")
            return max(min_troops, target_enemy + portion_troops - 1)
        else:
            write_log(self.clock, "AfterAttack", f"sharing src with other attack plan with no extra {idle_troops} troops, give up killing plan and average the troops based on border")
            return self.put_troops_on_border(src, tgt, max_troops, min_troops)

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
        if src not in self.threat_this_turn:
            write_log(self.clock, "AfterAttack", f"{src} is not in threat list, so stay 1 troops")
            return max_troops - 1
        if self.threat_this_turn[src]['is_door']:
            stay_troops = max(1, (2 + self.threat_this_turn[src]['enemy_troops']))
            moving_troops = max(min_troops, max_troops - stay_troops)
            write_log(self.clock, "AfterAttack", f"{src} is in threat list and is door, so stay {stay_troops} troops")
            return moving_troops
        else:
            stay_troops = max(1, (self.threat_this_turn[src]['enemy_troops']))
            moving_troops = max(min_troops, max_troops - stay_troops)
            write_log(self.clock, "AfterAttack", f"{src} is in threat list and is not door, so stay {stay_troops} troops")
            return moving_troops
        
    # Fortify
    def fortify_troops(self):
        tgts, group = self.find_weakest_territories()
        srcs = self.find_strongest_territories(tgts, group)
        if len(srcs) == 0:
            return 
        new_tgts = [tgt for tgt in tgts if self.state.territories[tgt].troops < self.state.territories[tgts[0]].troops + 2][:3]
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


def main():
    
    # Get the game object, which will connect you to the engine and
    # track the state of the game.
    game = Game()
    bot_state = BotState(game.state) 
    write_log("-1","Version", f"{VERSION}")

    # Respond to the engine's queries with your moves.
    while True:

        # Get the engine's query (this will block until you receive a query).
        query = game.get_next_query()
        
        bot_state.clock = list(query.update.keys())[0]

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
    bot_state.update_status()

    # step 1 Blocking other player occupied whole continentcheck if other player have the chance to dominent one specific continent
    territory = bot_state.block_players()
    if territory:
        write_log(bot_state.clock, "Claim", f"decided by block, {territory}")
        return game.move_claim_territory(query, territory)

    # step 2 check if we can dominent one specific continent
    name = bot_state.search_preferred_continent()
    if name:
        territory = bot_state.choose_adjacent_with_info(name)
        if territory is not None:
            write_log(bot_state.clock, "Claim", f"decided by collect continent, {territory}")
            return game.move_claim_territory(query, territory)
    
    # step 3 try to maximise the adjacent territory
    sorted_group = bot_state.get_sorted_connected_group(bot_state.territories[bot_state.id_me])
    territory = bot_state.try_to_connect_territory_no_gap(sorted_group)
    if territory:
        write_log(bot_state.clock, "Claim", f"decided by connect with possible largest territories, {territory}")
        return game.move_claim_territory(query, territory)
    
    territory = bot_state.try_to_connect_territory_1_gap(sorted_group)
    if territory:
        write_log(bot_state.clock, "Claim", f"decided by 1 gap with possible largest territories, {territory}")
        return game.move_claim_territory(query, territory)
    
    # step 4 pick by degree
    territory = bot_state.pick_by_degree()
    write_log(bot_state.clock, "Claim", f"decided by degree, {territory}")
    return game.move_claim_territory(query, territory)

def handle_place_initial_troop(game: Game, bot_state: BotState, query: QueryPlaceInitialTroop) -> MovePlaceInitialTroop:
    """
    After all the territories have been claimed, you can place a single troop on one
    of your territories each turn until each player runs out of troops.
    """

    # step 0 update status
    bot_state.update_status()

    # senario 1: we control full continent
    group = bot_state.check_full_control_continent()
    if group:
        territory_id = bot_state.put_troops_equally_on_border(group)
        write_log(bot_state.clock, "Initialise", f"equally distributed troops on the border of our continent {territory_id}")
        return game.move_place_initial_troop(query, territory_id)

    # senario 2: we have edge in a continent
    group = bot_state.check_our_dominent_continent()
    territory_id = bot_state.put_troops_equally_on_border(group)
    write_log(bot_state.clock, "Initialise", f"equally distributed troops on the border of our continent {territory_id}")
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

    # We need to remember we have to place our matching territory bonus if we have one.
    if len(game.state.me.must_place_territory_bonus) != 0:
        assert total_troops >= 2
        for i in game.state.me.must_place_territory_bonus:
            if i in game.state.get_territories_owned_by(game.state.me.player_id):
                distributions[i] += 2
                total_troops -= 2
                break
            
    # step 0 update all information
    bot_state.update_status()
    for pid in bot_state.id_all_player:
        bot_state.write_player_information(pid)
    
    # plan
    bot_state.plan_to_do()
    write_log(bot_state.clock, "Distribute", f"follow plan {bot_state.plan}")
    total_troops, distributions = bot_state.distribute_troops_by_plan(total_troops, distributions)

    return game.move_distribute_troops(query, distributions)

def handle_attack(game: Game, bot_state: BotState, query: QueryAttack) -> Union[MoveAttack, MoveAttackPass]:
    """
    After the troop phase of your turn, you may attack any number of times until you decide to
    stop attacking (by passing). After a successful attack, you may move troops into the conquered
    territory. If you eliminated a player you will get a move to redeem cards and then distribute troops.
    """
    bot_state.update_status()
    last_record = cast(RecordAttack, game.state.recording)[-1]
    if last_record.record_type == 'move_troops_after_attack':
        bot_state.plan_to_do()
    elif last_record.record_type != 'move_distribute_troops':
        bot_state.update_plan()
        if bot_state.plan is None and not bot_state.got_territoty_this_turn:
            bot_state.plan_to_do()
    write_log(bot_state.clock, 'Attack', f"plan: {bot_state.plan}")
    information = bot_state.attack_by_plan()
    if information is not None:
        attack_territory, target_territory, troops = information
        return game.move_attack(query, attack_territory, target_territory, troops)
    return game.move_attack_pass(query)
   

def handle_troops_after_attack(game: Game, bot_state: BotState, query: QueryTroopsAfterAttack) -> MoveTroopsAfterAttack:
    """
    After conquering a territory in an attack, you must move troops to the new territory.
    """
    bot_state.got_territoty_this_turn = True
    bot_state.update_status()
    bot_state.get_defending_continent_proposal()
    record_attack = cast(RecordAttack, game.state.recording[query.record_attack_id])
    move_attack = cast(MoveAttack, game.state.recording[record_attack.move_attack_id])
    moving_troops = bot_state.moving_troops_based_on_plan_code(record_attack, move_attack)


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

    bot_state.update_status()
    bot_state.got_territoty_this_turn = False
    information = bot_state.fortify_troops()
    if information is not None:
        src, tgt, troops = information
        return game.move_fortify(query, src, tgt, troops)
    return game.move_fortify_pass(query)



if __name__ == "__main__":
    main()