

(declare-fun N () Int)
(declare-fun N_next () Int)
(define-fun .n () Int (! N :next N_next))
(declare-fun i () Int)
(declare-fun i_next () Int)
(define-fun .i () Int (! i :next i_next))
(declare-fun Z () Int)
(declare-fun Z_next () Int)
(define-fun .Z () Int (! Z :next Z_next))


(declare-fun a_read (Int) Int)
(declare-fun a_read_next (Int) Int)
(define-fun .a_read () (! a_read :next a_read_next))

(declare-fun a_write (Int Int) Bool)
(declare-fun a_write_next (Int Int) Bool)
(define-fun .a_write () (! a_write :next a_write_next))

(declare-fun b_read (Int) Int)
(declare-fun b_read_next (Int) Int)
(define-fun .b_read () (! b_read :next b_read_next))

(declare-fun b_write (Int) Int)
(declare-fun b_write_next (Int) Int)
(define-fun .b_write () (! b_write :next b_write_next))


(define-fun init-conditions () Bool (!
 (and
  (= i 0)
  (> N 0)
) :init true))

(define-fun trans-conditions () Bool (!
 (and
  (< i N)
  (b_write i (a_read i))
  (forall (i v) (implies (a_write i v)
                         (= (a_read_next i) v)))
  (forall (i j v) (implies (and (not (= i j) (a_write i v)))
                           (= (a_read_next j) (a_read j))))
  (forall (i v) (implies (b_write i v)
                         (= (b_read_next i) v)))
  (forall (i j v) (implies (and (not (= i j) (b_write i v)))
                           (= (b_read_next j) (b_read j))))
  (= (+ i 1) i_next)
  (= a_read a_read_next)
  (= N N_next)
  (= Z Z_next)
  ) :trans true))

(define-fun property () Bool (!
 (and
  (=> (and (>= i n) (> Z 0) (< Z n)) (= (a_read Z) (b_read Z)))
) :invar-property 0))


