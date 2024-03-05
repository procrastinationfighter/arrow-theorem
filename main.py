from z3 import *
import itertools

x = Int("x")
a = Int("a")
b = Int("b")
c = Int("c")
s = Int("s")
s1 = Int("s1")
s2 = Int("s2")

def get_p():
    ## Function "p" is defined as follows:
    ## p(x, a, b, s) is true when in the situation s, agent x prefers a over b
    ## in other words, in situation s we have a >_x b 
    return Function("p", IntSort(), IntSort(), IntSort(), IntSort(), BoolSort())

def get_w():
    ## Function "w" is defined as follows:
    ## w(a, b, s) is true when in the situation s, a is preferred over b in social welfare function
    return Function("w", IntSort(), IntSort(), IntSort(), BoolSort())

p = get_p()
w = get_w()

def get_linearity():
    # Antisymmetric, strongly connected and not reflexive:
    # either a > b, b > a or a = b and never a > a or b > b
    first = Or(p(x, a, b, s), p(x, b, a, s), a == b)
    second = And(Not(p(x, a, a, s)), Not(w(a, a, s)))
    third = Or(w(a, b, s), w(b, a, s), a == b)

    # Transitive
    fourth = Implies(And(p(x, a, b, s), p(x, b, c, s)), p(x, a, c, s))
    fifth = Implies(And(w(a, b, s), w(b, c, s)), w(a, c, s))

    return ForAll([x, a, b, s, c], And(first, second, third, fourth, fifth))

def individual_prefs():
    assumption = ForAll([x, a, b], p(x, a, b, s1) == p(x, a, b, s2))
    result = ForAll([a, b], w(a, b, s1) == w(a, b, s2))

    return ForAll([s1, s2], Implies(assumption, result))

def get_unanimity():
    # unanimity: for every agent require that if a > b in state s,
    # then this will hold in result of social welfare function
    assumption = ForAll([x], p(x, a, b, s))
    return ForAll([a, b, s], Implies(assumption, w(a, b, s)))

def get_nondictatorship():
    # non-dictatorship: there is no such agent that all his preferences match
    condition = p(x, a, b, s) == w(a, b, s)
    return Not(Exists([x], ForAll([s, a, b], condition)))

def get_iia():
    # iia: if for every agent a > b, then this will hold in result of social welfare function
    assumption = ForAll([x], p(x, a, b, s1) == p(x, a, b, s2))
    return ForAll([a, b, s1, s2], Implies(assumption, w(a, b, s1) == w(a, b, s2)))

def get_swap():
    # swap function: swap(x, a, b, s) swaps the preference between a and b
    # in state s, for agent x; the result is a new state s' where this is true
    return Function("swap", IntSort(), IntSort(), IntSort(), IntSort(), IntSort())

swap = get_swap()

def get_swap_condition():
    # basic condition:
    basic = p(x, a, b, swap(x, a, b, s)) == p(x, b, a, s)
    # tl;dr Reiter's successor state axioms, linked in the paper

    # a condition for swap to work: for example if we have a > b > c
    # and swap(x, a, c, s), then we must guarantee that c > b > a now.
    # also, we must provide that this does not affect other relations
    a1 = Int("a1")
    b1 = Int("b1")
    y = Int("y")

    # If we swap and no change happens,
    # then either other agent did the swap or the swap did not concern these alternatives
    swap_part = p(x, a, b, swap(y, a1, b1, s)) == p(x, a, b, s)
    neq_part = Or(Not(x == y), And())
    not_affecting = And(swap_part, neq_part)

    # Guarantees, nothing interesting.
    first_g = And(x == y, a == a1, b == b1, p(x, b, a, s))
    second_g = And(x == y, a == a1, Not(b == b1), Not(b == a), p(x, b1, b, s))
    third_g = And(x == y, b == b1, Not(a == a1), Not(b == a), p(x, a, a1, s))

    return ForAll([x, y, a, a1, b, b1, s], And(basic, Or(not_affecting, first_g, second_g, third_g)))

def introduce_constants():
    permutations = itertools.permutations([1, 2, 3])
    constant_conditions = []
    curr_state = 0

    for first_perm in permutations:
        for second_perm in permutations:
            curr_state += 1
            first_agent = And(
                p(1, first_perm[0], first_perm[1], curr_state), 
                p(1, first_perm[0], first_perm[2], curr_state),
                p(1, first_perm[1], first_perm[2], curr_state)
                )
            second_agent = And(
                p(2, second_perm[0], second_perm[1], curr_state), 
                p(2, second_perm[0], second_perm[2], curr_state),
                p(2, second_perm[1], second_perm[2], curr_state)
                )
            constant_conditions.append(And(first_agent, second_agent))

    return And(constant_conditions)

def main():
    # Require that the preferences are linear
    linearity = get_linearity()

    # Confirm that function w aggregates individual preferences:
    ind = individual_prefs()

    unanimity = get_unanimity()
    nondictatorship = get_nondictatorship()
    iia = get_iia()
    
    swap_cond = get_swap_condition()

    constants = introduce_constants()

    main_sentence = And(linearity, ind, unanimity, nondictatorship, iia, swap_cond, constants)

    solve(main_sentence)

main()
