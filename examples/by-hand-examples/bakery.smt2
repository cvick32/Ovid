(declare-var state (Array Int Int))
(declare-var state1 (Array Int Int))
(declare-var token (Array Int Int))
(declare-var token1 (Array Int Int))
(declare-var i Int)
(declare-var j Int)
(declare-var next_token Int)
(declare-var next_token1 Int)
(declare-var to_serve Int)
(declare-var to_serve1 Int)

;; (define-const idle Int 0)
;; (define-const wait Int 1)
;; (define-const critical Int 2)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int Int))
(declare-rel fail ())

;;initial formula

;; (define-fun init () Bool
;; (!
;;     (forall ((i1 index))
;;         (and
;;             (= (state i1) idle)
;;             (= (token i1) 0)
;;             (= next_token 1)
;;             (= to_serve 1)
;;         )
;;     )
;; :init true)
;; )


(rule (=> (and (= state ((as const (Array Int Int)) 0))
               (= token ((as const (Array Int Int)) 0))
               (= next_token 1)
               (= to_serve 1))
          (inv state token next_token to_serve N)))


;;transition formula
;; (define-fun first-rule () Bool
;; (!
;;     (exists ((i1 index))
;;         (and
;;             (= (state i1) idle)
;;             (= (state^1 i1) wait)
;;             (= (token^1 i1) next_token)
;;             (= next_token^1  (+ next_token 1))
;;             (= to_serve  to_serve^1 )
;;             (forall ((j index))
;;                 (=>
;;                     (not (= i1 j))
;;                     (and
;;                         (= (state^1 j) (state  j))
;;                         (= (token^1 j) (token  j))
;;                     )
;;                 )
;;             )
;;         )
;;     )
;;     :action 1))


(rule (=> (and
           (inv state token next_token to_serve N)
           (< i N)
           (= (select state i) 0)
           (= (store state i 1) state1)
           (= (store token i next_token) token1)
           (= next_token1 (+ next_token 1))
           (= to_serve to_serve1))
          (inv state1 token1 next_token1 to_serve1 N)))

;; (define-fun second-rule () Bool
;; (!
;;     (exists ((i1 index))
;;         (and
;;             (= (state  i1) wait)
;;             (= (state^1 i1) critical)
;;             (= (token i1) to_serve )
;;             (= (token^1 i1) (token i1))
;;             (= next_token^1  next_token )
;;             (= to_serve  to_serve^1 )
;;             (forall ((j index))
;;                 (=>
;;                     (not (= i1 j))
;;                     (and
;;                         (= (state^1  j) (state  j))
;;                         (= (token^1  j) (token  j))
;;                     )
;;                 )
;;             )
;;         )
;;     )
;; :action 2))


(rule (=> (and
           (inv state token next_token to_serve N)
           (< i N)
           (= (select state i) 1)
           (= (store state i 2) state1)
           (= (select token i) to_serve)
           (= token token1)
           (= next_token1 next_token)
           (= to_serve1 to_serve)
          (inv state1 token1 next_token1 to_serve1 N)))

;; (define-fun third-rule () Bool
;; (!
;;     (exists ((i1 index))
;;         (and
;;             (= (state  i1) critical)
;;             (= (state^1  i1) idle)
;;             (= (token^1  i1) 0)
;;             (= next_token^1  next_token )
;;             (= to_serve^1 (+ to_serve 1))
;;             (forall ((j index))
;;                 (=>
;;                     (not (= i1 j))
;;                     (and
;;                         (= (state^1  j) (state  j))
;;                         (= (token^1  j) (token  j))
;;                     )
;;                 )
;;             )
;;         )
;;     )
;;     :action 3))

(rule (=> (and
           (inv state token next_token to_serve N)
           (< i N)
           (= (select state i) 2)
           (= (store state i 0) state1)
           (= (store token i 0) token1)
           (= next_token1 next_token)
           (= to_serve1 (+ to_serve 1)))
          (inv state1 token1 next_token1 to_serve1 N)))

;;(define-fun trans () Bool
;;    (or first-rule second-rule third-rule)
;; )

(rule (=> (and
           (inv state token next_token to_serve N)
           (< i N)
           (< j N)
           (not (= j i))
           (= (select state i) 2)
           (= (select state j) 2))
          fail))

(query fail)

;; (define-fun prop () Bool
;;   (!
;;     (forall ((i index) (j index))
;;         ( =>
;;             (not (= i j))
;;             (not (and
;;                 (= (state i) critical)
;;                 (= (state j) critical)
;;                 )
;;             )
;;         )
;;     )
;; :invar-property 0))

;; (define-fun unsafe-1 () Bool
;; (!

;;  (forall ((i index) (j index))
;;     ( =>
;;         (not (= i j))
;;         (not (and
;;             (= (state i) idle)
;;             (= (state j) wait)
;;         ))
;;     )
;;     )
;; :invar-property 1))

;; (define-fun unsafe-2 () Bool
;; (!
;;  (forall ((i index) (j index))
;;     ( =>
;;         (not (= i j))
;;         (not (and
;;             (= (state i) critical)
;;             (= (state j) wait)
;;         ))
;;     )
;;  )
;; :invar-property 2))

;; (define-fun unsafe-3 () Bool
;; (!
;;  (forall ((i index) (j index))
;;     ( =>
;;         (not (= i j))
;;         (not (and
;;             (= (state i) idle)
;;             (= (state j) critical)
;;             (> next_token 4)
;;             (= (token j) (token i))
;;         ))
;;     )
;;  )
;; :invar-property 3))

;; (define-fun safe-4 () Bool
;; (!
;;  (forall ((i index))
;;         (not (and
;;             (= (state i) idle)
;;             (> (token i) 1)
;;         ))

;;  )
;; :invar-property 4))

;; (define-fun safe-5 () Bool
;; (!
;;  (forall ((i index) (j index))
;;     ( =>
;;         (and
;;             (not (= i j))
;;             (= (token i) (token j))
;;         )
;;             (= (token i) 0)
;;     ))
;; :invar-property 5))

;; (define-fun safe-2 () Bool
;; (!
;;  (forall ((i index))
;;         (not (and
;;             (= (state i) 4)
;;             (= (token i) 0)
;;         ))
;;     )
;; :invar-property 6))


;; (define-fun prop-inductive () Bool
;; (!
;;     (forall ((i index) (j index))
;;        (or
;;             (= i j)


;;        (and

;;         ( =>
;;             (not (= i j))
;;             (not (and
;;                 (= (state i) critical)
;;                 (= (state j) critical)
;;             ))
;;         )

;;         (<=
;;            1
;;            (+ next_token (* (- 1) (token i)))
;;         )

;;         (or
;;             (= i j)
;;             (not (= to_serve (token j)))
;;             (not (= to_serve (token i)))
;;            (= (state j) 0)
;;         )

;;         (or
;;             (= i j)
;;             (not (= to_serve (token i)))
;;             (not (= (state j) 2))
;;         )

;;         (or
;;             (= i j)
;;             (= (state i) 0)
;;             (not (= (token i) (token j)))
;;         )

;;         (not (= next_token (token i)))

;;         (or
;;             (<= 1 (token j))
;;             (= (token j) 0)
;;         )

;;     )))
;; :invar-property 7))
