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

VERSION = '3.0.0'
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

# help function
def write_log(game, msg):
    if DEBUG:
        with open(game.log, 'a') as f:
            f.write(f"{msg}\n")
    else:
        print(msg, flush=True)

def group_connected_territories(mt, state):
    def DFS_visit(u):
        visited[u] = True 
        for v in state.map.get_adjacent_to(u):
            if v in visited and not visited[v]:
                parent[v] = u
                group.append(v)
                DFS_visit(v)

    visited, parent = {}, {}
    for u in mt:
        visited[u], parent[u] = False, None
    groups = []
    for u in mt:
        group = []
        if not visited[u]:
            DFS_visit(u)
        groups.append(group)
    return groups 

def get_percentage_to_continent(mt, name):
    return len(set(CONTINENT[name]) & set(mt))/len(CONTINENT[name])

class Bot:
    def __init__(self, state):
        self.state = state
        self.id_me = None
        self.ids_others = []
        self.territories = {}
        self.adjacent_territories = []
        self.border_territories = []

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
    
    # Put troops
    def put_troops_equally_on_border_with_information(self, group):
        borders = self.state.get_all_border_territories(group)
        return min(borders, key=lambda x:self.state.territories[x].troops)

    def check_full_control_continent(self):
        groups = self.get_sorted_connected_group()
        for name in CONTINENT:
            for g in groups:
                if get_percentage_to_continent(g, name) > 0.98:
                    return g
        return None
    
# We will store our enemy in the bot state.
class BotState():
    def __init__(self):
        self.enemy: Optional[int] = None


def main():
    
    # Get the game object, which will connect you to the engine and
    # track the state of the game.
    game = Game()
    bot_state = BotState()
    bot = Bot(game.state) 
    game.bot = bot
    game.log = './log.txt'

    # Respond to the engine's queries with your moves.
    while True:

        # Get the engine's query (this will block until you receive a query).
        query = game.get_next_query()

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
        write_log(game, f"decided by block, {territory}")
        return game.move_claim_territory(query, territory)

    # step 2 check if we can dominent one specific continent
    territories = game.bot.search_preferred_continent()
    if territories:
        territory = game.bot.choose_adjacent_with_info(territories)
        write_log(game, f"decided by collect continent, {territory}")
        return game.move_claim_territory(query, territory)
    
    # step 3 try to maximise the adjacent territory
    sorted_group = game.bot.get_sorted_connected_group()
    territory = game.bot.try_to_connect_territory_no_gap(sorted_group)
    if territory:
        write_log(game, f"decided by connect with possible largest territories, {territory}")
        return game.move_claim_territory(query, territory)
    
    territory = game.bot.try_to_connect_territory_1_gap(sorted_group)
    if territory:
        write_log(game, f"decided by 1 gap with possible largest territories, {territory}")
        return game.move_claim_territory(query, territory)
    
    # step 4 pick by degree
    territory = game.bot.pick_by_degree()
    write_log(game, f"decided by degree, {territory}")
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
        territory_id = game.bot.put_troops_equally_on_border_with_information(group)
        write_log(game.log, f"equally distributed troops on the border of our continent {territory_id}")
        return game.move_place_initial_troop(query, territory_id)


    # Get whole territories
    owned_territories = game.state.get_territories_owned_by(game.state.me.player_id)

    # Check our border.
    border_territories = game.state.get_all_border_territories(owned_territories)

    # Check our dominent continent
    # key_territories = players_dominant_continent(owned_territories)
    # if key_territories:
    #     candidates = list(set(border_territories) & set(key_territories))
    #     if candidates:
    #         return game.move_place_initial_troop(query, candidates[0])

    # We will place troops along the territories on our border.

    # We will place a troop in the border territory with the least troops currently
    # on it. This should give us close to an equal distribution.
    border_territory_models = [game.state.territories[x] for x in border_territories]
    min_troops_territory = min(border_territory_models, key=lambda x: x.troops)

    return game.move_place_initial_troop(query, min_troops_territory.territory_id)


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

    # We will distribute troops across our border territories.
    total_troops = game.state.me.troops_remaining
    distributions = defaultdict(lambda: 0)
    border_territories = game.state.get_all_border_territories(
        game.state.get_territories_owned_by(game.state.me.player_id)
    )

    # We need to remember we have to place our matching territory bonus
    # if we have one.
    if len(game.state.me.must_place_territory_bonus) != 0:
        assert total_troops >= 2
        distributions[game.state.me.must_place_territory_bonus[0]] += 2
        total_troops -= 2


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
    
    # We will attack someone.
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    bordering_territories = game.state.get_all_adjacent_territories(my_territories)

    def attack_weakest(territories: list[int]) -> Optional[MoveAttack]:
        # We will attack the weakest territory from the list.
        territories = sorted(territories, key=lambda x: game.state.territories[x].troops)
        for candidate_target in territories:
            candidate_attackers = sorted(list(set(game.state.map.get_adjacent_to(candidate_target)) & set(my_territories)), key=lambda x: game.state.territories[x].troops, reverse=True)
            for candidate_attacker in candidate_attackers:
                if game.state.territories[candidate_attacker].troops > 1:
                    return game.move_attack(query, candidate_attacker, candidate_target, min(3, game.state.territories[candidate_attacker].troops - 1))


    if len(game.state.recording) < 4000:
        # We will check if anyone attacked us in the last round.
        new_records = game.state.recording[game.state.new_records:]
        enemy = None
        for record in new_records:
            match record:
                case MoveAttack() as r:
                    if r.defending_territory in set(my_territories):
                        enemy = r.move_by_player

        # If we don't have an enemy yet, or we feel angry, this player will become our enemy.
        if enemy != None:
            if bot_state.enemy == None or random.random() < 0.05:
                bot_state.enemy = enemy
        
        # If we have no enemy, we will pick the player with the weakest territory bordering us, and make them our enemy.
        else:
            weakest_territory = min(bordering_territories, key=lambda x: game.state.territories[x].troops)
            bot_state.enemy = game.state.territories[weakest_territory].occupier
            
        # We will attack their weakest territory that gives us a favourable battle if possible.
        enemy_territories = list(set(bordering_territories) & set(game.state.get_territories_owned_by(enemy)))
        move = attack_weakest(enemy_territories)
        if move != None:
            return move
        
        # Otherwise we will attack anyone most of the time.
        if random.random() < 0.8:
            move = attack_weakest(bordering_territories)
            if move != None:
                return move

    # In the late game, we will attack anyone adjacent to our strongest territories (hopefully our doomstack).
    else:
        strongest_territories = sorted(my_territories, key=lambda x: game.state.territories[x].troops, reverse=True)
        for territory in strongest_territories:
            move = attack_weakest(list(set(game.state.map.get_adjacent_to(territory)) - set(my_territories)))
            if move != None:
                return move

    return game.move_attack_pass(query)


def handle_troops_after_attack(game: Game, bot_state: BotState, query: QueryTroopsAfterAttack) -> MoveTroopsAfterAttack:
    """
    After conquering a territory in an attack, you must move troops to the new territory.
    """
    
    # First we need to get the record that describes the attack, and then the move that specifies
    # which territory was the attacking territory.
    record_attack = cast(RecordAttack, game.state.recording[query.record_attack_id])
    move_attack = cast(MoveAttack, game.state.recording[record_attack.move_attack_id])

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
    shortest_path = find_shortest_path_from_vertex_to_set(game, most_troops_territory, set(game.state.get_territories_owned_by(most_powerful_player)))
    # We will move our troops along this path (we can only move one step, and we have to leave one troop behind).
    # We have to check that we can move any troops though, if we can't then we will pass our turn.
    if len(shortest_path) > 0 and game.state.territories[most_troops_territory].troops > 1:
        return game.move_fortify(query, shortest_path[0], shortest_path[1], game.state.territories[most_troops_territory].troops - 1)
    else:
        return game.move_fortify_pass(query)


def find_shortest_path_from_vertex_to_set(game: Game, source: int, target_set: set[int]) -> list[int]:
    """Used in move_fortify()."""

    # We perform a BFS search from our source vertex, stopping at the first member of the target_set we find.
    queue = deque()
    queue.appendleft(source)

    current = queue.pop()
    parent = {}
    seen = {current: True}

    while len(queue) != 0:
        if current in target_set:
            break

        for neighbour in game.state.map.get_adjacent_to(current):
            if neighbour not in seen:
                seen[neighbour] = True
                parent[neighbour] = current
                queue.appendleft(neighbour)

        current = queue.pop()

    path = []
    while current in parent:
        path.append(current)
        current = parent[current]

    return path[::-1]

if __name__ == "__main__":
    main()