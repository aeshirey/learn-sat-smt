# Learn SAT/SMT
_This is a work-in-progress!_

## About this document
Many of the videos I've seen and documents I've read when trying to learn SAT/SMT are far too in-depth to help newbies, so I started this to organize my own thoughts, to learn more about SAT/SMT, and to be an aid to others in the same.

This document is intended to be introductory yet detailed enough for individuals wanting to learn practical SAT/SMT. It is not exhaustive in its use of [different logics](http://smtlib.cs.uiowa.edu/logics.shtml), [solvers](http://smtlib.cs.uiowa.edu/solvers.shtml), use cases, s-expressions, and so on.

For the sake of not getting caught in the weeds, I may be incomplete in definitions or distinctions. I generally use the term `SMT` to cover both it and `SAT`. I also am fairly new to this topic, so if I make gross errors, please create an issue, submit a pull request fixing it, or drop me a line.

My intent is to make this document accessible to most software developers in the language and examples I use. I use [Z3](https://github.com/Z3Prover/z3) by Microsoft Research, though I expect any reasonable SAT solver can be substituted. SAT/SMT examples will use either s-expressions directly or the [Python API for Z3](https://pypi.org/project/z3-solver/).

## Who is the target audience?
In short: people who program and are interested in optimization problems.

This document assumes you have a reasonable understanding of propositional logic and Boolean arithmetic, including `and`, `or`, `not`, `xor`, `implies`, and `iff` operators; [De Morgan's Laws](https://en.wikipedia.org/wiki/De_Morgan%27s_laws); set theory; and more. If it's been many years since your computer science degree, or if you don't have a theoretical background, no worries -- if you are comfortable using and reading Boolean expressions, you're probably fine. Two simple examples of Boolean expressions might be:

```csharp
bool can_drive_car = has_license || (age >= 15 && has_learners_permit);
```

```python
is_arguing = contrary_position and series_of_statements and not no_it_isnt
```

As boolean algebra, these would be written with logical notation as:

$$
can\_drive\_car = has\_license \vee (age \ge 15 \wedge has\_learners\_permit)
$$

$$
is\_arguing = contrary\_position \wedge series\_of\_statements \wedge \neg no\_it\_isnt
$$

## What is SAT?
`SAT` is short for [Boolean SATisfiability problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem) -- "determining if there exists an interpretation that satisfies a given Boolean formula". In other words, given a number of related true/false statements, SAT determines if it's possible to satisfy the combination of those statements, and if so, how.

For example, if we want to satisfy the second example above (`is_arguing==True`), we can do so with the following values:

* `contrary_position == True`
* `series_of_statements == False`
* `no_it_isnt == False`

This expression is _satisfiable_ (or just _sat_). But what if we _also_ had set `series_of_statements=False`? In that case, we cannot satisfy `is_arguing`; it is _unsatisfiable_, or _unsat_ because there is no combination of values that satisfy the desired final state of `is_arguing==True`.

There's power in identifying both _sat_ and _unsat_ situations: a model that returns _sat_ can return concrete inputs that may provide useful. On the other hand, an _unsat_ proves the non-existence of a solution; this might be useful in identifying that only a certain set of inputs will satisfy the constraints, after which no more solutions are possible.


## What is SMT?

[Satisfiability Modulo Theories](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories), or SMT, is an extension of SAT by "determining whether a mathematical formula is satisfiable." It generalizes SAT to include "real numbers, integers, and/or various data structures such as lists, arrays, bit vectors, and strings."

Consider, then, the first example above. If we want to find a value of `age` that satisfies our propositions given certain other restrictions:

* `can_drive_car == true`
* `has_license == false`
* `has_learners_permit == true`
* `age == ?`

We can use SMT to confirm that this input is, in fact, _sat_, and we can find a concrete value for `age`. For these propositions, any value of `age >= 15` will suffice. While the solver will provide one concrete value (eg, 15), isn't necessarily the only one.

For the remainder of this document, the term `SMT` will be used for the general description of what we're doing. When the distinction needs to be made, I will call it out.

## Mechanics
_Note: This section gives some detail on how SAT works under the hood - notably, CNF - that may be useful as you read other documentation. You can safely skip this section if you want._

SMT is encoded as a set of _[s-expressions](https://en.wikipedia.org/wiki/S-expression)_ (or s-exprs). These s-exprs are then passed to a _solver_ to process them. Internally, the solver will parse the s-expr text; normalize them all to _[conjunctive normal form](https://en.wikipedia.org/wiki/Conjunctive_normal_form)_ (for SAT); simplify the internal representation; and find values that satisfy the constraints, if possible, or return _unsat_.

Conjunctive normal form (CNF) is a standardized notation for boolean expressions, comprising only `and`, `or`, and `not` operators. The normalization is that CNF is a _conjunction_ (boolean `and`, also written as $ \wedge $) of a series of _disjunctive_ (boolean `or`, written as $ \vee $) expressions. Consider the `implies` logicial proposition $p \implies q$ (read "p implies q"), which means "if p is true, then q is true". But if p is false, there is no requirement on q for the implication to hold. This can be represented with the [truth table](https://en.wikipedia.org/wiki/Truth_table):

| $p$ | $q$ | $p \implies q$ |
|-----|-----|----------------|
| false | false | true  | 
| false | true  | true  | 
| true  | false | false | 
| true  | true  | true  | 

$p \implies q$ can thus be normalized to CNF:

    or (and (not p) (not q))
       (and (not p) q)
       (and p q)

Or, more simply:

    or (not p)
       (and p q)

With this basic info established, let's move on to [basic s-expressions](/01%20Basic%20s-exprs.md).