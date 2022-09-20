(declare-fun cell (Int Int) Int)

(assert (and
    (<= 1 (cell 1 1)) (>= 9 (cell 1 1))
    (<= 1 (cell 1 2)) (>= 9 (cell 1 2))
    (<= 1 (cell 1 3)) (>= 9 (cell 1 3))
    (<= 1 (cell 1 4)) (>= 9 (cell 1 4))
    (<= 1 (cell 1 5)) (>= 9 (cell 1 5))
    (<= 1 (cell 1 6)) (>= 9 (cell 1 6))
    (<= 1 (cell 1 7)) (>= 9 (cell 1 7))
    (<= 1 (cell 1 8)) (>= 9 (cell 1 8))
    (<= 1 (cell 1 9)) (>= 9 (cell 1 9))
    (<= 1 (cell 2 1)) (>= 9 (cell 2 1))
    (<= 1 (cell 2 2)) (>= 9 (cell 2 2))
    (<= 1 (cell 2 3)) (>= 9 (cell 2 3))
    (<= 1 (cell 2 4)) (>= 9 (cell 2 4))
    (<= 1 (cell 2 5)) (>= 9 (cell 2 5))
    (<= 1 (cell 2 6)) (>= 9 (cell 2 6))
    (<= 1 (cell 2 7)) (>= 9 (cell 2 7))
    (<= 1 (cell 2 8)) (>= 9 (cell 2 8))
    (<= 1 (cell 2 9)) (>= 9 (cell 2 9))
    (<= 1 (cell 3 1)) (>= 9 (cell 3 1))
    (<= 1 (cell 3 2)) (>= 9 (cell 3 2))
    (<= 1 (cell 3 3)) (>= 9 (cell 3 3))
    (<= 1 (cell 3 4)) (>= 9 (cell 3 4))
    (<= 1 (cell 3 5)) (>= 9 (cell 3 5))
    (<= 1 (cell 3 6)) (>= 9 (cell 3 6))
    (<= 1 (cell 3 7)) (>= 9 (cell 3 7))
    (<= 1 (cell 3 8)) (>= 9 (cell 3 8))
    (<= 1 (cell 3 9)) (>= 9 (cell 3 9))
    (<= 1 (cell 4 1)) (>= 9 (cell 4 1))
    (<= 1 (cell 4 2)) (>= 9 (cell 4 2))
    (<= 1 (cell 4 3)) (>= 9 (cell 4 3))
    (<= 1 (cell 4 4)) (>= 9 (cell 4 4))
    (<= 1 (cell 4 5)) (>= 9 (cell 4 5))
    (<= 1 (cell 4 6)) (>= 9 (cell 4 6))
    (<= 1 (cell 4 7)) (>= 9 (cell 4 7))
    (<= 1 (cell 4 8)) (>= 9 (cell 4 8))
    (<= 1 (cell 4 9)) (>= 9 (cell 4 9))
    (<= 1 (cell 5 1)) (>= 9 (cell 5 1))
    (<= 1 (cell 5 2)) (>= 9 (cell 5 2))
    (<= 1 (cell 5 3)) (>= 9 (cell 5 3))
    (<= 1 (cell 5 4)) (>= 9 (cell 5 4))
    (<= 1 (cell 5 5)) (>= 9 (cell 5 5))
    (<= 1 (cell 5 6)) (>= 9 (cell 5 6))
    (<= 1 (cell 5 7)) (>= 9 (cell 5 7))
    (<= 1 (cell 5 8)) (>= 9 (cell 5 8))
    (<= 1 (cell 5 9)) (>= 9 (cell 5 9))
    (<= 1 (cell 6 1)) (>= 9 (cell 6 1))
    (<= 1 (cell 6 2)) (>= 9 (cell 6 2))
    (<= 1 (cell 6 3)) (>= 9 (cell 6 3))
    (<= 1 (cell 6 4)) (>= 9 (cell 6 4))
    (<= 1 (cell 6 5)) (>= 9 (cell 6 5))
    (<= 1 (cell 6 6)) (>= 9 (cell 6 6))
    (<= 1 (cell 6 7)) (>= 9 (cell 6 7))
    (<= 1 (cell 6 8)) (>= 9 (cell 6 8))
    (<= 1 (cell 6 9)) (>= 9 (cell 6 9))
    (<= 1 (cell 7 1)) (>= 9 (cell 7 1))
    (<= 1 (cell 7 2)) (>= 9 (cell 7 2))
    (<= 1 (cell 7 3)) (>= 9 (cell 7 3))
    (<= 1 (cell 7 4)) (>= 9 (cell 7 4))
    (<= 1 (cell 7 5)) (>= 9 (cell 7 5))
    (<= 1 (cell 7 6)) (>= 9 (cell 7 6))
    (<= 1 (cell 7 7)) (>= 9 (cell 7 7))
    (<= 1 (cell 7 8)) (>= 9 (cell 7 8))
    (<= 1 (cell 7 9)) (>= 9 (cell 7 9))
    (<= 1 (cell 8 1)) (>= 9 (cell 8 1))
    (<= 1 (cell 8 2)) (>= 9 (cell 8 2))
    (<= 1 (cell 8 3)) (>= 9 (cell 8 3))
    (<= 1 (cell 8 4)) (>= 9 (cell 8 4))
    (<= 1 (cell 8 5)) (>= 9 (cell 8 5))
    (<= 1 (cell 8 6)) (>= 9 (cell 8 6))
    (<= 1 (cell 8 7)) (>= 9 (cell 8 7))
    (<= 1 (cell 8 8)) (>= 9 (cell 8 8))
    (<= 1 (cell 8 9)) (>= 9 (cell 8 9))
    (<= 1 (cell 9 1)) (>= 9 (cell 9 1))
    (<= 1 (cell 9 2)) (>= 9 (cell 9 2))
    (<= 1 (cell 9 3)) (>= 9 (cell 9 3))
    (<= 1 (cell 9 4)) (>= 9 (cell 9 4))
    (<= 1 (cell 9 5)) (>= 9 (cell 9 5))
    (<= 1 (cell 9 6)) (>= 9 (cell 9 6))
    (<= 1 (cell 9 7)) (>= 9 (cell 9 7))
    (<= 1 (cell 9 8)) (>= 9 (cell 9 8))
    (<= 1 (cell 9 9)) (>= 9 (cell 9 9))
))

; Row checks
(assert (distinct (cell 1 1) (cell 1 2) (cell 1 3) (cell 1 4) (cell 1 5) (cell 1 6) (cell 1 7) (cell 1 8) (cell 1 9))) ; row 1
(assert (distinct (cell 2 1) (cell 2 2) (cell 2 3) (cell 2 4) (cell 2 5) (cell 2 6) (cell 2 7) (cell 2 8) (cell 2 9))) ; row 2
(assert (distinct (cell 3 1) (cell 3 2) (cell 3 3) (cell 3 4) (cell 3 5) (cell 3 6) (cell 3 7) (cell 3 8) (cell 3 9))) ; etc
(assert (distinct (cell 4 1) (cell 4 2) (cell 4 3) (cell 4 4) (cell 4 5) (cell 4 6) (cell 4 7) (cell 4 8) (cell 4 9)))
(assert (distinct (cell 5 1) (cell 5 2) (cell 5 3) (cell 5 4) (cell 5 5) (cell 5 6) (cell 5 7) (cell 5 8) (cell 5 9)))
(assert (distinct (cell 6 1) (cell 6 2) (cell 6 3) (cell 6 4) (cell 6 5) (cell 6 6) (cell 6 7) (cell 6 8) (cell 6 9)))
(assert (distinct (cell 7 1) (cell 7 2) (cell 7 3) (cell 7 4) (cell 7 5) (cell 7 6) (cell 7 7) (cell 7 8) (cell 7 9)))
(assert (distinct (cell 8 1) (cell 8 2) (cell 8 3) (cell 8 4) (cell 8 5) (cell 8 6) (cell 8 7) (cell 8 8) (cell 8 9)))
(assert (distinct (cell 9 1) (cell 9 2) (cell 9 3) (cell 9 4) (cell 9 5) (cell 9 6) (cell 9 7) (cell 9 8) (cell 9 9)))

; Column checks
(assert (distinct (cell 1 1) (cell 2 1) (cell 3 1) (cell 4 1) (cell 5 1) (cell 6 1) (cell 7 1) (cell 8 1) (cell 9 1))) ; column 1
(assert (distinct (cell 1 2) (cell 2 2) (cell 3 2) (cell 4 2) (cell 5 2) (cell 6 2) (cell 7 2) (cell 8 2) (cell 9 2))) ; column 2
(assert (distinct (cell 1 3) (cell 2 3) (cell 3 3) (cell 4 3) (cell 5 3) (cell 6 3) (cell 7 3) (cell 8 3) (cell 9 3))) ; etc
(assert (distinct (cell 1 4) (cell 2 4) (cell 3 4) (cell 4 4) (cell 5 4) (cell 6 4) (cell 7 4) (cell 8 4) (cell 9 4)))
(assert (distinct (cell 1 5) (cell 2 5) (cell 3 5) (cell 4 5) (cell 5 5) (cell 6 5) (cell 7 5) (cell 8 5) (cell 9 5)))
(assert (distinct (cell 1 6) (cell 2 6) (cell 3 6) (cell 4 6) (cell 5 6) (cell 6 6) (cell 7 6) (cell 8 6) (cell 9 6)))
(assert (distinct (cell 1 7) (cell 2 7) (cell 3 7) (cell 4 7) (cell 5 7) (cell 6 7) (cell 7 7) (cell 8 7) (cell 9 7)))
(assert (distinct (cell 1 8) (cell 2 8) (cell 3 8) (cell 4 8) (cell 5 8) (cell 6 8) (cell 7 8) (cell 8 8) (cell 9 8)))
(assert (distinct (cell 1 9) (cell 2 9) (cell 3 9) (cell 4 9) (cell 5 9) (cell 6 9) (cell 7 9) (cell 8 9) (cell 9 9)))

; Square checks
(assert (distinct (cell 1 1) (cell 1 2) (cell 1 3) (cell 2 1) (cell 2 2) (cell 2 3) (cell 3 1) (cell 3 2) (cell 3 3))) ; top left square
(assert (distinct (cell 1 4) (cell 1 5) (cell 1 6) (cell 2 4) (cell 2 5) (cell 2 6) (cell 3 4) (cell 3 5) (cell 3 6))) ; top middle square
(assert (distinct (cell 1 7) (cell 1 8) (cell 1 9) (cell 2 7) (cell 2 8) (cell 2 9) (cell 3 7) (cell 3 8) (cell 3 9))) ; etc
(assert (distinct (cell 4 1) (cell 4 2) (cell 4 3) (cell 5 1) (cell 5 2) (cell 5 3) (cell 6 1) (cell 6 2) (cell 6 3)))
(assert (distinct (cell 4 4) (cell 4 5) (cell 4 6) (cell 5 4) (cell 5 5) (cell 5 6) (cell 6 4) (cell 6 5) (cell 6 6)))
(assert (distinct (cell 4 7) (cell 4 8) (cell 4 9) (cell 5 7) (cell 5 8) (cell 5 9) (cell 6 7) (cell 6 8) (cell 6 9)))
(assert (distinct (cell 7 1) (cell 7 2) (cell 7 3) (cell 8 1) (cell 8 2) (cell 8 3) (cell 9 1) (cell 9 2) (cell 9 3)))
(assert (distinct (cell 7 4) (cell 7 5) (cell 7 6) (cell 8 4) (cell 8 5) (cell 8 6) (cell 9 4) (cell 9 5) (cell 9 6)))
(assert (distinct (cell 7 7) (cell 7 8) (cell 7 9) (cell 8 7) (cell 8 8) (cell 8 9) (cell 9 7) (cell 9 8) (cell 9 9)))

; To solve the puzzle @ http://www.websudoku.com/?level=4&set_id=1673273073
; we'll take the input data, which can be visualized as:
;    .4.2.....
;    93..7.5..
;    6....1...
;    ..5..7.26
;    ..9...3..
;    42.6..9..
;    ...5....1
;    ..8.6..93
;    .....8.7.

; When a number is known -- such as (row 1, column 2) = 2 -- then 
; we'll constrain the solution to use this knowledge:
(assert (= 4 (cell 1 2)))
(assert (= 2 (cell 1 4)))
(assert (= 9 (cell 2 1)))
(assert (= 3 (cell 2 2)))
(assert (= 7 (cell 2 5)))
(assert (= 5 (cell 2 7)))
(assert (= 6 (cell 3 1)))
(assert (= 1 (cell 3 6)))
(assert (= 5 (cell 4 3)))
(assert (= 7 (cell 4 6)))
(assert (= 2 (cell 4 8)))
(assert (= 6 (cell 4 9)))
(assert (= 9 (cell 5 3)))
(assert (= 3 (cell 5 7)))
(assert (= 4 (cell 6 1)))
(assert (= 2 (cell 6 2)))
(assert (= 6 (cell 6 4)))
(assert (= 9 (cell 6 7)))
(assert (= 5 (cell 7 4)))
(assert (= 1 (cell 7 9)))
(assert (= 8 (cell 8 3)))
(assert (= 6 (cell 8 5)))
(assert (= 9 (cell 8 8)))
(assert (= 3 (cell 8 9)))
(assert (= 8 (cell 9 6)))
(assert (= 7 (cell 9 8)))

(check-sat)
(get-model)
