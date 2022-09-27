# `assert-soft`
In addition to [`assert`](/03%20assert.md), SMT-LIB allows for "soft assertions" either with no weight specified (default 1):

```
(assert-soft (not p))
```

Or with a positive natural number, such as:

```
(assert-soft (not p) :weight 3)
(assert-soft q       :weight 1.5)
```

## Order of assertions
The soft assertions could be considered 'preferences' for the solution. Here's a simple example:

```
(declare-const i Int)
(declare-const j Int)

(assert-soft (< i j))
(assert-soft (< j i))

(check-sat)
sat

(get-model)
(
  (define-fun j () Int
    1)
  (define-fun i () Int
    0)
)
```

We've declared that we want both $i < j$ and $j < i$ -- two mutually-exclusive propositions, which with an `assert` would have returned _unsat_. But it works fine here, as the first proposition was satisfied.

Note what happens if the ordering is switched:

```
(declare-const i Int)
(declare-const j Int)

(assert-soft (< j i))
(assert-soft (< i j))

(check-sat)
sat

(get-model)
(
  (define-fun j () Int
    0)
  (define-fun i () Int
    1)
)
```

Now, we instead get $j < i$ satisfied and not $i < j$. The order of the assertions matters.

## Weights
`assert-soft` can take a `:weight n` value, a positive real value that indicates how strongly the soft assertion should be considered. All other things being equal, soft assertions with larger `weight` values are more likely to be met than are those with smaller values.

```
(declare-const i Int)
(declare-const j Int)

(assert-soft (< j i) :weight 1)
(assert-soft (< i j) :weight 1.1)

(check-sat)
sat

(get-model)
(
  (define-fun j () Int
    0)
  (define-fun i () Int
    (- 1))
)
```
---

For the next step, let's move from satisfying constraints to [optimizing them](/11%20Optimization.md). (This is apparently [limited to Z3 and is not in the SMT-LIB spec](https://stackoverflow.com/questions/71551539/when-will-the-smt-lib-standard-be-extended-to-include-optimization).)
