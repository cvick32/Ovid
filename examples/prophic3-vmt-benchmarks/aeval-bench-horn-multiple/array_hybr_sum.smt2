(declare-fun a () (Array Int Int))
(declare-fun a_next () (Array Int Int))
(define-fun .a () (Array Int Int) (! a :next a_next))
(declare-fun i () Int)
(declare-fun i_next () Int)
(define-fun .i () Int (! i :next i_next))
(declare-fun j () Int)
(declare-fun j_next () Int)
(define-fun .j () Int (! j :next j_next))
(declare-fun N () Int)
(declare-fun N_next () Int)
(define-fun .N () Int (! N :next N_next))
(declare-fun pc () Int)
(declare-fun pc_next () Int)
(define-fun .pc () Int (! pc :next pc_next))
(declare-fun Z () Int)
(declare-fun Z_next () Int)
(define-fun .Z () Int (! Z :next Z_next))

(define-fun init-conditions () Bool (!
 (and
(= i 0)
(> N 0)
(= pc 2)
) :init true))

(define-fun trans-conditions () Bool (!
 (and
(=> (and (< i N) (= pc 2)) (= (store a i i) a_next))
(=> (and (>= i N) (= pc 2)) (= a a_next))
(=> (and (< i N) (= pc 1)) (= a a_next))
(=> (and (= pc 1) (not (< i N))) (= a a_next))
(=> (and (< i N) (= pc 2)) (= (+ i 1) i_next))
(=> (and (>= i N) (= pc 2)) (= 0 i_next))
(=> (and (< i N) (= pc 1)) (= (+ i 1) i_next))
(=> (and (= pc 1) (not (< i N))) (= i i_next))
(=> (and (< i N) (= pc 2)) (= j j_next))
(=> (and (>= i N) (= pc 2)) (= 0 j_next))
(=> (and (< i N) (= pc 1)) (= (+ j (select a i)) j_next))
(=> (and (= pc 1) (not (< i N))) (= j j_next))
(= N N_next)
(=> (and (< i N) (= pc 2)) (= 2 pc_next))
(=> (and (>= i N) (= pc 2)) (= 1 pc_next))
(=> (and (< i N) (= pc 1)) (= 1 pc_next))
(=> (and (= pc 1) (not (< i N))) (= pc pc_next))
(= Z Z_next)
(or (= pc 2) (= pc 1))
) :trans true))

(define-fun property () Bool (!
 (and
(let ((a!1 (and (not (not (>= j 0))))))
  (=> (and (= pc 1) (>= i N)) a!1))
) :invar-property 0))

