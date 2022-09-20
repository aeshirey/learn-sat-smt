## Functions
A function in SMT-LIB can be defined or declared. `define-fun` contains the function's term (ie, the body of the function), such as this simple implementation of integer modulo plus an example of its use:

```
(define-fun % ((a Int) (b Int)) Int 
	(- a (* b (div a b))))

(declare-const three Int)
(assert (= three (% 7 4)))
```

This creates a function that has a predefined logic to it: we calculate the `%` of two Int sorts as being $ a - b * (a/b) $ (with integer division being performed with `div`).

A `declare-fun` expression omits the term and is used with assertions and arguments:

```
(declare-fun item_counts (Int) Int))

(assert (>= (item_counts 1) 0))
(assert (>= (item_counts 2) 0))
(assert (>= (item_counts 3) 0))
(assert (>= (item_counts 4) 0))
(assert (>= (item_counts 5) 0))
(assert (>= (item_counts 6) 0))

(assert (= 15.05
        (+
         (* 2.15 (item_counts 1)) ; mixed_fruit
         (* 2.75 (item_counts 2)) ; french_fries
         (* 3.35 (item_counts 3)) ; side_salad
         (* 3.55 (item_counts 4)) ; hot_wings
         (* 4.20 (item_counts 5)) ; mozzarella_sticks
         (* 5.80 (item_counts 6)) ; sampler_plate
        )))

(check-sat)
sat
(get-model)
(
  (define-fun item_counts ((x!0 Int)) Int
    (ite (= x!0 1) 1
    (ite (= x!0 4) 2
    (ite (= x!0 6) 1
      0))))
)
```

The s-expression returned for the `item_counts` function uses the `ite` (if-then-else) s-expr nested multiple times. This is the same as if we were writing some C# code:

```csharp
int item_counts(int x0)
{
    if (x0 == 1)
        return 1;
    else if (x0 == 4)
        return 2;
    else if (x0 == 6)
        return 1;
    else
        return 0;
}
```

Declaring functions in this way provides a good way to abstract collections of items: in the above example, `item_counts` is a unary function that accepts an Int sort and returns an Int sort, but we can think of it like an `int[]` array.
