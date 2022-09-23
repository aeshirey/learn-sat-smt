# Constants and Sorts
What we call "variables" in most programming languages, SMT-LIB calls "constants". These constants are each of a particular type, called a "sort". The "Int sort", for example, is defined in the SMT-LIB Standard:

> The set of values for the Int sort consists of all numerals and all terms of the form (- n) where n is a numeral other than 0.

That is to say, the Int sort covers all mathematical integers (_not_ 32- or 64-bit machine integers!): `5` is an Int, as are `(- 123)` and `18446744073709551616` (which exceeds [the maximum value of an unsigned 64 bit integer](https://learn.microsoft.com/en-us/dotnet/api/system.uint64.maxvalue?view=net-6.0))

SAT, dealing with boolean propositions, makes use of the Bool sort. SMT, on the other hand, uses Bool, Int, Real, and others.

We can declare constants in SMT with `declare-const`:

```
(declare-const a Int)
```

When using the Python API, we can create the `a` constant using the Z3 `Int` function, providing the name we want to use:

```python
from z3 import *
a = Int('a')
```

The Python API also provides functions such as `Ints` and `Bools` to allow the concise declaration of multiple constants:

```python
a, b, c = Ints('a b c')
x, y = Reals('x y')
```

These declarations -- in SMT-LIB or Python -- specify the constant name and sort, but their values are (currently) unrestricted: we haven't imposed any constraints on what values of `a` will satisfy our model. We can do this with some assertions.

---
Knowing how to create constants, we can next use [assert expressions](/03%20assert.md) to constrain them.