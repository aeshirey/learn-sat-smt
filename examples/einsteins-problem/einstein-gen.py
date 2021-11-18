#!/usr/binb/python3

"""
Code to generate SMT-LIB s-expressions. 
See my post @ https://aeshirey.github.io/code/2021/11/17/solving-einstein-s-problem-with-smt.html
Code found  @ https://github.com/aeshirey/learn-sat-smt
"""

parameters = {
    'colors': ['blue', 'green', 'red', 'white', 'yellow'],
    'nationalities': ['brit', 'dane', 'german', 'norwegian', 'swede'],
    'beverage': ['beer', 'coffee', 'milk', 'tea', 'water'],
    'cigar': ['bluemaster', 'dunhill', 'pallmall', 'prince', 'blend'],
    'pet': ['cat', 'bird', 'dog', 'fish', 'horse']
}


def has_neighbor(prop1: str, prop2: str) -> str:
    """
    Builds the statements required for: The person who `prop1` has a neighbor who `prop2`.
    For example, "The Norwegian lives next to the Blue house."

    We can solve this by doing a disjunction of all satisfying possibilities. Because we've
    previously stated that, for example, there's only one Norwegian and only one blue house,
    we don't need to conjoin to prevent duplicates. Thus, we can say:

    ```ignore
    (assert (or
        (and (norwegian 1) (blue 2))
        (and (norwegian 2) (blue 1))
        (and (norwegian 2) (blue 3))
        (and (norwegian 3) (blue 2))
        (and (norwegian 3) (blue 4))
        ...
    ))
    ```
    """
    ands = []
    for i in range(1, 6):
        for j in range(1, 6):
            if abs(i-j) == 1:
                ands.append(f'    (and ({prop1} {i}) ({prop2} {j}))')

    return '(assert (or\n' \
        + '\n'.join(ands) \
        + '))\n'


# declare each function
for (k, vs) in parameters.items():
    print(f'; functions for {k}:')
    for v in vs:
        print(f'(declare-fun {v} (Int) Bool)')
    print()

# every parameter must match exactly one house
for (k, vs) in parameters.items():
    # k might be 'colors', vs are the list of those colors
    for v in vs:
        # v might be 'blue'
        # (blue 1) or (blue 2) or ... or (blue 5)
        ors = ' '.join(f'({v} {i})' for i in range(1, 6))

        # at least one of these must be true: blue1 || blue2 || ...
        print(f'; at least one {v} house')
        print(f'(assert (or {ors}))')

        # but we can't have more than one true. we do this by saying:
        # !(blue1 && blue2) && !(blue1 && blue3) && ...
        # !(blue2 && blue3) && !(blue2 && blue4) && ...
        print(f'; but not more than one {v} house')
        for i in range(1, 5):
            for j in range(i+1, 6):
                print(f'(assert (not (and ({v} {i}) ({v} {j}))))')
        print()

    # We've made it so exactly one house must be blue, but now we declare that
    # if a house is blue, it can't also be red. This should look something like:
    # (assert (not (and (blue 1) (green 1))))
    # (assert (not (and (blue 1) (red 1))))
    # ...
    print(f'; A house can only match one {k} proposition')
    for v1 in vs:
        for v2 in vs:
            if v1 != v2:
                for i in range(1, 6):
                    print(f"(assert (not (and ({v1} {i}) ({v2} {i}))))")
    print()


# Encode the clues
print(';1. The Brit lives in a Red house.')
for i in range(1, 6):
    print(f'(assert (iff (brit {i}) (red {i})))')
print()

print(';2. The Swede keeps Dogs as pets.')
for i in range(1, 6):
    print(f'(assert (iff (swede {i}) (dog {i})))')
print()

print(';3. The Dane drinks Tea.')
for i in range(1, 6):
    print(f'(assert (iff (dane {i}) (tea {i})))')
print()

print(';4. The Green house is on the left of the White house.')
print('(assert (or\n'
      + '\n'.join(f'    (and (green {i}) (white {i+1}))' for i in range(1, 5))
      + '\n))\n')

print(';5. The Green house owner drinks Coffee.')
for i in range(1, 6):
    print(f'(assert (iff (green {i}) (coffee {i})))')
print()

print(';6. The owner who smokes Pall Mall rears Birds.')
for i in range(1, 6):
    print(f'(assert (iff (pallmall {i}) (bird {i})))')
print()

print(';7. The owner of the Yellow house smokes Dunhill.')
for i in range(1, 6):
    print(f'(assert (iff (yellow {i}) (dunhill {i})))')
print()

print(';8. The owner living in the center house drinks Milk.')
print('(assert (milk 3))\n')

print(';9. The Norwegian lives in the first house.')
print('(assert (norwegian 1))\n')

print(';10. The owner who smokes Blend lives next to the one who keeps Cats.')
print(has_neighbor('blend', 'cat'))

print(';11. The owner who keeps horses lives next to the man who smokes Dunhill.')
print(has_neighbor('horse', 'dunhill'))

print(';12. The owner who smokes Bluemaster drinks Beer.')
for i in range(1, 6):
    print(f'(assert (iff (bluemaster {i}) (beer {i})))')
print()

print(';13. The German smokes Prince.')
for i in range(1, 6):
    print(f'(assert (iff (german {i}) (prince {i})))')
print()

print(';14. The Norwegian lives next to the Blue house.')
print(has_neighbor('norwegian', 'blue'))

print(';15. The owner who smokes Blend has a neighbor who drinks Water.')
print(has_neighbor('blend', 'water'))



# Answer the question 'Who keeps fish?'
print('(declare-const owns_fish Int)')
print('(assert (fish owns_fish))')

print('(assert (or')
for i in range(1, 6):
    print(f'(= {i} owns_fish)')
print('))\n')

print('(declare-const natl_owns_fish String)')
print('(assert (= natl_owns_fish')
print('    (ite (brit owns_fish) "brit"')
print('    (ite (dane owns_fish) "dane"')
print('    (ite (german owns_fish) "german"')
print('    (ite (norwegian owns_fish) "norwegian" "swede"))))')
print('))\n')


print('(check-sat)')
print('(get-model)\n')
print(";(eval owns_fish) ; displays '4' when run")
print("(eval natl_owns_fish) ; 'german'")