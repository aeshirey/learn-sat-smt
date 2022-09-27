# Solving Optimizations

SMT solvers also have the `minimize` and `maximize` s-expressions that can be used to find optimal solutions instead of any satisfying set of values.

This example comes from [Modeling of Optimization Problems using an SMT solver](https://www.youtube.com/watch?v=xF1Df21pr9A):

> An oil company has a contract to deliver 100000 litres of gasoline. Their tankers can carry 2400 litres and they can attach one trailer carrying 2200 litres to each tanker.
> 
> All the tankers and trailers must be completely full on this contract, otherwise the gas would slosh around too much when going over some rough roads.
>
> Find the least number of tankers required to fulfill the contract.
>
> [Each trailer, if used, must be pulled by a full tanker.]

This equation for this word problem is:

$$
100000 = 2400*tankers + 2200*trailers
$$

With the added constraints that:
* tankers >= trailers (every trailer must be pulled by a tanker, but not every tanker needs to pull a trailer)
* trailers >= 0 (we can't have negative trailers)

By now, this should be easy to encode in s-expressions:
```
(declare-const num_tankers Int)
(declare-const num_trailers Int)

(assert (>= num_tankers num_trailers))
(assert (> num_trailers 0))
(assert (= 100000 (+ (* num_tankers 2400)
                     (* num_trailers 2200))))

(check-sat)
sat

(get-model)
(
  (define-fun num_trailers () Int
    4)
  (define-fun num_tankers () Int
    38)
)
```

Or in Python:

```python
from z3 import *
tankers, trailers = Ints('tankers trailers')
s = Solver()
s.add(tankers > trailers,
      trailers >= 0,
      100_000 == tankers*2400 + trailers*2200)

assert sat == s.check() 
s.model() # [tankers = 38, trailers = 4]
```


But this isn't guaranteed to be the _optimal_ solution (which we define as the fewest number of tankers). This can be achieved with `(minimize num_tankers)`:

```
(minimize num_tankers)
(check-sat)
sat

(get-model)
(
  (define-fun num_trailers () Int
    16)
  (define-fun num_tankers () Int
    27)
)
```

The Python implementation makes use of the [`Optimize` class](https://z3prover.github.io/api/html/classz3py_1_1_optimize.html) instead of the [`Solver`]():

```python
from z3 import *
tankers, trailers = Ints('tankers trailers')
o = Optimize()
o.add(tankers > trailers,
      trailers >= 0,
      100_000 == tankers*2400 + trailers*2200)

h = o.minimize(tankers)

assert sat == o.check() 
o.model() # [tankers = 27, trailers = 16]
h.value() # 27
```

---

Let's now revisit rectangle packing, applying SMT optimizations to solve [bin packing](/12%20bin-packing.py).