# SMT-LIB Reference

Below is an incomplete list of expressions you may need along with their arity/signature, an example, and possible notes.

The Arity column shows the numeric arity and the signature in `(argument-sorts) return-sort`. For example, `not` receives one boolean (`(Bool)`) and returns a boolean (`Bool`).

| Expression | Arity | Example | Notes |
|------------|-------|---------|-------|
| (Binary math) | n            | `(+ 1 1 2 3 5 8)`         | |
| `not`         | 1, (Bool) Bool | `(not p)`                 | |
| `implies`     | 2, (Bool Bool) Bool | `(implies rain umbrella)` | |
| `iff`         | 2, (Bool Bool) Bool  | `(iff monty-python completely-different)` | Bidirectional implication; `iff` holds true only when both arguments are the same |
| `ite`         | 3, (Bool S S) S  | `(ite big 300 20)` | If-then-else; returns the first `S` value if the boolean holds, or the second value otherwise.
| `distinct` | n | `(distinct x y z)` | All arguments are distinct from one another |
| `forall` | 2, (List of Sorts, Bool) | | Represents universal quantifier, $\forall$ |

---

# Additional Resources
* [SMT-LIB Language Standard](http://smtlib.cs.uiowa.edu/language.shtml)
* [Z3 API in Python](https://ericpony.github.io/z3py-tutorial/guide-examples.htm) ([project page on GitHub](https://github.com/ericpony/z3py-tutorial)) - a backup of the now-offline official Z3Py webpage
* [Getting Started with Z3: A Guide](https://www.philipzucker.com/z3-rise4fun/guide.html)
* [SMT-LIB: a Brief Tutorial](https://link.springer.com/content/pdf/bbm:978-3-662-50497-0/1.pdf) [pdf]
