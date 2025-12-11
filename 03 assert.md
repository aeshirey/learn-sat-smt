# `assert` expression

The `assert` unary s-expression accepts a Bool sort and is how SAT and SMT propositions are used to constrain your solution. For example, if you want to find a value $a \mid a \gt 10 \wedge a \lt 5$, you could provide the assertions:

```
(declare-const a Int)
(assert (> a 10))
(assert (< a 5))
(check-sat) ; unsat
```

This set of conjoined propositions is _unsatisfiable_: There exists no value of `a` that is both greater than 10 and less than five.

We can see this also in the Python implementation:

```python
from z3 import *
a = Int('a')
s = Solver()
s.add(a > 10, a < 5)
assert(unsat == s.check())
```

---


With this in mind, let's try a simple example: [is this number prime?](/04%20Example%3A%20Prime%20check.md).
