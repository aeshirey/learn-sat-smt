My more detailed post [is available here](https://aeshirey.github.io/code/2021/11/17/solving-einstein-s-problem-with-smt.html).

```bash
# Generate the s-expressions to define the problem
$ python3 einstein-gen.py > einstein-generated.smt2

# Run the SAT solver
$ z3 einstein-generated.smt2 > einstein-model.txt

# Check out the results
$ head einstein-model.txt
sat
(
  (define-fun owns_fish () Int
    4)
  (define-fun natl_owns_fish () String
    "german")
  (define-fun brit ((x!0 Int)) Bool
    (= x!0 3))
  (define-fun bluemaster ((x!0 Int)) Bool
    (= x!0 5))
```