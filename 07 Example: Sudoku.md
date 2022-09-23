# Example: Sudoku
Something a bit more complicated is solving Sudoku, which is a problem very well-suited to SAT because there are a few very clearly-defined rules (ie, constraints) that guide the game:

1. There are 81 cells in a 9x9 square,
2. Each square holds a value 1-9,
3. Each row, column, and 3x3 sub-square must contain the values 1-9 with no value duplicated

Consider the solution, written as s-expressions. We could either declare each cell:

```
(declare-const cell_1_1 Int)
(declare-const cell_1_2 Int)
(declare-const cell_1_3 Int)
; and so on
(declare-const cell_9_9 Int)
```

Or we could declare a single function:

```
; passed the row and column, returns the value
(declare-fun cell (Int Int) Int)

; for example, if the value in row 4, column 8 is 1:
(assert (= 1 (cell 4 8)))
```

For clarity, the latter approach is better.

## Overall constraints
How might the game rules be encoded as s-expressions?

**There are 81 cells in a 9x9 square** can be implicit by the values passed to the function. We'll only call the `cell` function with valid inputs.

**Each square holds a value 1-9** requires that every cell be constrained to be `>= 1` and `<= 9`.

```
(assert (and
    (<= 1 (cell 1 1)) (>= 9 (cell 1 1))
    (<= 1 (cell 1 2)) (>= 9 (cell 1 2))
    (<= 1 (cell 1 3)) (>= 9 (cell 1 3))
    ; and so on
```

**Each row, column, and 3x3 sub-square must contain the values 1-9 with no value duplicated** could be written as a few thousand comparisons, asserting that values `i` and `j` in the same row must be unequal:

```
; Values in row 1 must be distinct
(assert (not (= (cell 1 1) (cell 1 2))))
(assert (not (= (cell 1 1) (cell 1 3))))
(assert (not (= (cell 1 1) (cell 1 4))))
(assert (not (= (cell 1 1) (cell 1 5))))
(assert (not (= (cell 1 1) (cell 1 6))))
(assert (not (= (cell 1 1) (cell 1 7))))
(assert (not (= (cell 1 1) (cell 1 8))))
(assert (not (= (cell 1 1) (cell 1 9))))
(assert (not (= (cell 1 2) (cell 1 3))))
(assert (not (= (cell 1 2) (cell 1 4))))
; and so on

; Values in row 2 must be distinct
(assert (not (= (cell 2 1) (cell 2 2))))
; etc
```

This can be done fairly easily with the Python API or even programmatically generating SMT-LIB code. But as we're writing the SMT-LIB code ourselves, there's the `distinct` function that can be used:

```
; Values in row 1 must be distinct
(assert (distinct (cell 1 1)
                  (cell 1 2)
                  (cell 1 3)
                  (cell 1 4)
                  (cell 1 5)
                  (cell 1 6)
                  (cell 1 7)
                  (cell 1 8)
                  (cell 1 9)))
; Values in row 2 must be distinct
; (similar to above)
```

This still requires some verbosity but is manageable.

Finally, with a concrete set of given values, we can restrict the solution to just the puzzle we're solving. Using [this input puzzle](http://www.websudoku.com/?level=4&set_id=1673273073), we know that row 1, column 2 must be 4:

```
(assert (= 4 (cell 1 2)))
```

![puzzle](/resources/sudoku_blank.png)

A full SMT-LIB implementation (comprising 432 boolean assertions) [can be found here](/07%20sudoku.smt2).

## Python implementation
The equivalent Python implementation -- with helpful output display -- is reproduced here:

```python
from z3 import *

s = Solver()
cell = Function('cell', *(IntSort(), IntSort()), IntSort())

# Every row and column must be >= 1 and <= 9
for r in range(1, 10):
    for c in range(1, 10):
        s.add(cell(r,c) >= 1, cell(r,c) <= 9)

# every row must be distinct
for r in range(1, 10):
    s.add(Distinct([cell(r, c) for c in range(1, 10)]))

# every column must be distinct
for c in range(1, 10):
    s.add(Distinct([cell(r, c) for r in range(1, 10)]))

# every 3x3 sub-square must be distinct
for rsq in range(3):
    for csq in range(3):
        s.add(Distinct([
            cell(rsq*3+1, csq*3+1), cell(rsq*3+1, csq*3+2), cell(rsq*3+1, csq*3+3),
            cell(rsq*3+2, csq*3+1), cell(rsq*3+2, csq*3+2), cell(rsq*3+2, csq*3+3),
            cell(rsq*3+3, csq*3+1), cell(rsq*3+3, csq*3+2), cell(rsq*3+3, csq*3+3),
            ]))

puzzle = [
        '.4.2.....',
        '93..7.5..',
        '6....1...',
        '..5..7.26',
        '..9...3..',
        '42.6..9..',
        '...5....1',
        '..8.6..93',
        '.....8.7.'
        ]

for r in range(1, 10):
    for c in range(1, 10):
        value = puzzle[r-1][c-1]
        if value != '.':
            s.add(cell(r,c) == int(value))

assert(sat == s.check())
m = s.model()

'''
Print the solution, such as:

    847|253|169
    931|476|582
    652|891|734
    ---+---+---
    185|937|426
    769|142|358
    423|685|917
    ---+---+---
    376|529|841
    518|764|293
    294|318|675
'''
for r in range(1, 10):
    values = [m.eval(cell(r, c)).as_string() for c in range(1, 10)]

    values[6:6] = '|'
    values[3:3] = '|'

    print(''.join(values))
    if r in [3,6]: print('---+---+---')
```

---

For the next example, we'll work on an NP-Complete problem that is conceptually simple in SMT: the [rectangle packing problem](/08%20Example%3A%20Rectangle%20Packing.md).
