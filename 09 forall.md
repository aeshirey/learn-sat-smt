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

What if we want SMT to find some number, $n > 5$, such that _n_ is prime? Clearly, declaring a new constant and asserting that $n \ne i*j$ won't work:

```
(declare-const i Int)
(declare-const j Int)
(declare-const n Int) ; new
(assert (> i 1))
(assert (> j 1))
(assert (not (= n (* i j))))
(assert (> n 5))

(check-sat)
sat

(get-model)
(
  (define-fun i () Int
    10)
  (define-fun n () Int
    6)
  (define-fun j () Int
    16)
)
```

This has simply found two values of _i_ and _j_ whose product doesn't equal some other integer, _n_. What we need is a way to declare:

$$
n \in \mathbb{Z} \mid \forall i \in \mathbb{Z^{2+}}, \forall j \in \mathbb{Z^{2+}}, n \ne i*j
$$

That is to say, find some _n_ in the set of (non-negative) integers such that for all values of _i_ and _j_ greater than or equal to two, _n_ is not a product of _i_ and _j_.

This definition can be translated into SMT-LIB code using the `forall` expression, which is given "a non-empty list of variables, which abbreviates a sequential nesting of quantifiers". Or, given some list of variables over which `forall` operates, we can apply some assertions:


```
(declare-const n Int)
(assert (> n 5))

(assert (forall ((i Int) (j Int))
        (or (< i 2)
            (< j 2)
            (< n i)
            (< n j)
            (not (= n (* i j))))))
(check-sat)
sat

(get-model)
(
  (define-fun n () Int
    7)
)
```

The `forall` expression reasons about all possible combinations of integer values _i_ and _j_ and requires that for every pair, either:
* _i_ or _j_ is less than 2, meaning they can't possibly be prime factors of _n_, or
* _i_ or _j_ is greater than _n_, similarly not prime factors by definition, or
* the product of _i_ and _j_ doesn't equal _n_

We can scale this up to, say, $n > 10000$:

```
(declare-const n Int)
(assert (> n 10000))

(assert (forall ((i Int) (j Int))
        (or (< i 2)
            (< j 2)
            (< n i)
            (< n j)
            (not (= n (* i j))))))
(check-sat)
sat

(get-model)
(
  (define-fun n () Int
    10007)
)
```
