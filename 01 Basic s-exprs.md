# s-expr declarations
SMT logic is specified in the [SMT-LIB language](http://smtlib.cs.uiowa.edu/language.shtml) as a series of s-expressions. Here are some examples that you can enter interactively with `z3 -in`:

```
; this is a comment
(assert true)
(check-sat)
(get-model)
(exit)
```

This series of s-exprs makes one assertion (`true`), checks that this is satisfiable (it is), and gets the model (an empty set of values, which is rather uninteresting).

The same thing using the Python API could be written as:

```python
from z3 import *
s = Solver() # create a solver object
s.add(True) # add a True assertion
assert(sat == s.check()) # check that our assertions are satisfiable
```

S-expressions each have an "[arity](https://en.wikipedia.org/wiki/Arity)" -- the number of "arguments" they take. For example, you can see that `assert` is given the `true` argument; it has an arity of 1. `check-sat`, `get-model`, and `exit` have no arguments; thus, their arity is 0 (sometimes called _nullary_). _n-ary_ expressions take a variable number of arguments, such as `(+ 1 2 3 4)`.

---

Next up: [Constants and Sorts](/02%20Constants%20and%20Sorts.md).