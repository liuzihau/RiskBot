import random
DICE = [1, 2, 3, 4, 5, 6]

def attack_simulater(a, d):    
    compare_count = min(a, d)
    a_dices = [random.choice(DICE) for _ in range(a)]
    d_dices = [random.choice(DICE) for _ in range(d)]
    a_dices.sort(reverse=True)
    d_dices.sort(reverse=True)
    a_loss, d_loss = 0, 0
    for i in range(compare_count):
        if a_dices[i] > d_dices[i]:
            d_loss += 1
        else:
            a_loss += 1
    return a_loss, d_loss

def situation(a, d, three_dices_restriction=False):
    while a > 0 and d > 0:
        if a > 2:
            a_dice = 3
        elif a == 0 or three_dices_restriction:
            return a, d
        else:
            a_dice = a
        
        if d > 1:
            d_dice = 2
        elif d == 0:
            return a, d
        else:
            d_dice = 1
        
        a_loss, d_loss = attack_simulater(a_dice, d_dice)
        a -= a_loss
        d -= d_loss
    return a, d

def test_probability(a, d):
    atk_win, def_win, draw = 0, 0, 0
    test_count = 100000
    for _ in range(test_count):
        a_loss, d_loss = attack_simulater(a, d)
        if a_loss == 0:
            atk_win += 1
        elif d_loss == 0:
            def_win += 1
        else:
            draw += 1
    print(f"test count: {test_count}, P(atk win): {atk_win/test_count}, P(def win): {def_win/test_count}, , P(draw): {draw/test_count}")

def test_situation1():
    atk_remain = 0
    def_remain = 0
    test_count = 100000
    for _ in range(test_count):
        attacker = 44
        defender = [3, 3, 3, 3, 3, 3]
        final_territories = []
        i = 0
        while i < len(defender):
            final_territories.append(1)
            attacker, defender[i] = situation(attacker - 1, defender[i])
            if defender[i] > 0:
                break
            else:
                attacker -= 1
            i += 1
        final_territories.append(attacker)
        atk_remain += sum(final_territories)
        def_remain += sum(defender)
    return atk_remain / test_count, def_remain / test_count
        
def test_situation2():
    atk_remain = 0
    def_remain = 0
    test_count = 100000
    attacker = 14
    defender = 14
    for _ in range(test_count):
        a , d = situation(attacker, defender, True)
        atk_remain += a
        def_remain += d
    return atk_remain / test_count - attacker, def_remain / test_count - defender

def test_situation3():
    atk_win = 0
    count = 0
    test_count = 10000
    attacker = 16
    defender = 10
    for _ in range(test_count):
        a , d = situation(attacker, defender, True)
        # print(a, d)
        if d == 0:
            atk_win += 1
        count += 1
    return atk_win / count
if __name__ == "__main__":
    print(test_situation3())