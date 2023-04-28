
(declare-fun i () Int)
(declare-fun i_next () Int)
(define-fun .i () Int (! i :next i_next))

(declare-fun a (Int) Int)
(declare-fun b (Int) Int)

(declare-fun n () Int)
(declare-fun n_next () Int)
(define-fun .n () Int (! n :next n_next))
(declare-fun Z () Int)
(declare-fun Z_next () Int)
(define-fun .Z () Int (! Z :next Z_next))

(define-fun init-conditions () Bool (!
 (and
  (= i 0)
  (> n 0)
) :init true))

(define-fun trans-conditions () Bool (!
 (and
  (= (b i) (a i))
  (< i n)
  (= (+ i 1) i_next)
  (= n n_next)
  (= Z Z_next)) :trans true))

(define-fun property () Bool (!
 (and
(let ((a!1 (not (not (= (a Z) (b Z))))))
  (=> (and (>= i n) (> Z 0) (< Z n)) (and a!1)))
) :invar-property 0))

