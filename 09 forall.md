# `forall`

Consider our first example: [checking if a number is prime](/04%20Example%3A%20Prime%20check.md), which looks like this:

```
(declare-const i Int)
(declare-const j Int)
(assert (> i 1))
(assert (> j 1))
(assert (= 117 (* i j)))

(check-sat)
sat

(get-model)
(
  (define-fun j () Int
    13)
  (define-fun i () Int
    9)
)
```

What if we want SMT to find some number, $n > 10000$, such that _n_ is prime? Clearly, declaring a new constant and asserting that $n \ne i*j$ won't work:

```
(declare-const i Int)
(declare-const j Int)
(declare-const n Int) ; new
(assert (> i 1))
(assert (> j 1))
(assert (not (= n (* i j))))

(check-sat)
sat

(get-model)
(
  (define-fun n () Int
    5)
  (define-fun i () Int
    2)
  (define-fun j () Int
    2)
)
```

This has simply found two values of _i_ and _j_ whose product doesn't equal some other integer, _n_. What we need is a way to declare:

$$
n \in \mathbb{Z} \mid \forall i \in \mathbb{Z^{2+}}, \forall j \in \mathbb{Z^{2+}}, n \ne i*j
$$

That is to say, find some _n_ in the set of (non-negative) integers such that for all values of _i_ and _i_ greater than or equal to two, _n_ is not a product of _i_ and _j_.

This definition can be translated into SMT-LIB code using the `forall` expression, which is given "a non-empty list of variables, which abbreviates a sequential nesting
of quantifiers". Or, given some list of variables over which `forall` operates, we can apply some assertions:

```
(declare-const n Int)
(assert (> n 10000))

(assert (forall ((i Int) (j Int))
        (or (<= 2 i)
            (<= 2 j)
            (> n i)
            (> n j)
            (not (= n (* i j))))))
(check-sat)
sat

(get-model)
(
  (define-fun n () Int
    10001)
)
```

Note that we're restricting _i_ and _j_ to be `>= 2` and `< n`. These constraints are definitional: as potential factors of _n_, they must be greater than one and may not exceed _n_. They are also practical, though: restricting the domain of _i_ and _j_ allows Z3 to more efficiently reason about what _n_ is, given that it is greater than the (potential) factors _i_ and _j_. Indeed, omitting the `(> n i)` and `(> n i)` assertions prevents Z3 from being able to check satisfiability:

```
(declare-const n Int)
(assert (> n 10000))

(assert (forall ((i Int) (j Int))
        (or (<= 2 i)
            (<= 2 j)
            (not (= n (* i j))))))
(check-sat)
unknown
```