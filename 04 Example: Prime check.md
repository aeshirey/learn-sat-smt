# Example: Is _n_ prime?
Let's try to do something useful: determine whether the number 117 is prime. If it's composite, then there should be two factors $ i,j \mid i*j = 117 $. Thus, we will know that 117 is prime if it is unsatisfiable to find any two values of `i` and `j`:

```
(declare-const i Int)
(declare-const j Int)
(assert (= 117 (* i j)))
(check-sat); sat
```

Thus, 117 is not prime. The model will tell us the two factors it found:

```
(get-model)
(
  (define-fun j () Int
    1)
  (define-fun i () Int
    117)
)
```

There are two things to recognize:
* Internally, our solver actually represents our constants as nullary functions -- they take no arguments but return an Int sort. Knowing this will help you read model output.
* The values returned don't match our definition of primality: we need to explicitly exclude 1 when checking if n is prime. Thus, we'll add in two new assertions:

```
(assert (> i 1))
(assert (> j 1))
(check-sat)
sat
(get-model)
(
  (define-fun j () Int
    3)
  (define-fun i () Int
    39)
)
```

This looks better. What if we wanted to check for another solution? we know that $ 39*3=117 $, but are there any other factors we might use?

We can simply add in additional constraints that preclude this set of values. Here, we'll add in a single assertion against these two values:

```
(assert (not (and
    (= j 3)
    (= i 39)
    )))
(check-sat)
sat
(get-model)
(
  (define-fun i () Int
    13)
  (define-fun j () Int
    9)
)
```

This new assertion is saying, "require also that it's not the case that i=39 and j=3". The result is now that i=13, j=9.

Again, we can do this in Python. Creating multiple Ints can be achieved with the `Ints` function. Multiple assertions can be made together, and we can get the model if satisfiable:

```python
from z3 import *
i, j = Ints('i j')
s = Solver()
s.add(
    i > 1,
    j > 1,
    i*j == 117
)
assert(sat == s.check())
s.model() # [j = 39, i = 3]
```

---

Another example that might seem daunting but is quite easy is [the XKCD 'NP-Complete' problem](/05%20Example%3A%20NP-Complete.md).