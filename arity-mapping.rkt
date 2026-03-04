#lang plait

(require "HashSet.rkt"
         "cps-partition-arity.rkt")

; We can assume that the operator will never be a lambda from. It will be variables.

(define-type LV
  (lv [var-to-ref : (Hashof Var (HashSet Lab))]
      [lab-to-var : (Hashof Lab (HashSet Var))]))

(gen-map : (ULam UExp -> LV))
(define (gen-map f e)
  (let ([res (top-level f e)])
    (lv (fst res)
        (snd res))))

(top-level : (ULam UExp -> ((Hashof Var (HashSet Lab)) * (Hashof Lab (HashSet Var)))))
(define (top-level f e)
  (type-case UExp e
    [(u-lam l) (let ([res (ulam-map l
                                    (hash empty)
                                    (hash empty))])
                 (ulam-map f
                           (fst res)
                           (snd res)))]
    [(u-var v) (error 'top-level "free variable")]
    [else (ulam-map f
                    (hash empty)
                    (hash empty))]))

(ulam-map : (ULam (Hashof Var (HashSet Lab))
                  (Hashof Lab (HashSet Var)) ->
                  ((Hashof Var (HashSet Lab)) * (Hashof Lab (HashSet Var)))))
(define (ulam-map lam vtr ltv)
  (type-case ULam lam
    [(ulam l us k c)
     (call-map c
               vtr
               ltv
               (cons (cvv k)
                     (map (λ (v) (uvv v)) us)))]))

(clam-map : (CLam (Hashof Var (HashSet Lab))
                  (Hashof Lab (HashSet Var))
                  (Listof Var)->
                  ((Hashof Var (HashSet Lab)) * (Hashof Lab (HashSet Var)))))
(define (clam-map lam vtr ltv vl)
  (type-case CLam lam
    [(clam l us c)
     (call-map c
               vtr
               ltv
               (append vl (map (λ (v) (uvv v)) us)))]))

(call-map : (Call (Hashof Var (HashSet Lab))
                  (Hashof Lab (HashSet Var))
                  (Listof Var)->
                  ((Hashof Var (HashSet Lab)) * (Hashof Lab (HashSet Var)))))
(define (call-map c vtr ltv vl)
  (type-case Call c
    [(u-call uc)
     (type-case UCall uc
       [(ucall f e q l)
        (type-case UExp f
          [(u-var uv)
           (type-case CExp q
             [(c-lam cl) (clam-map cl
                                   (add-ref vtr
                                            (cons (uvv uv)
                                                  (append (uexp-uvar e) vl))
                                            (ul l))
                                   (hash-set ltv (ul l) (list-to-set vl))
                                   vl)]
             [(c-var cv) (pair (add-ref vtr
                                        (cons (uvv uv)
                                              (cons (cvv cv)
                                                    (append (uexp-uvar e) vl)))
                                        (ul l))
                               (hash-set ltv
                                         (ul l)
                                         (list-to-set vl)))])]
          [(u-lam l)
           (error 'call-map "f should not be a lambda in CPS.")]
          [else
           (error 'call-map "f should not be a number or boolean in CPS.")])]
       [(uif c t e lab)
        (type-case UExp c
          [(u-var uv)
           (type-case CExp t
             [(c-lam λ)
              (type-case CLam λ
                [(clam l us c)
                 (let ([fst-res (call-map c
                                          (add-ref vtr
                                                   vl
                                                   (ul lab))
                                          (hash-set ltv
                                                    (ul lab)
                                                    (list-to-set vl))
                                          vl)])
                   (type-case CExp e
                     [(c-lam λ2)
                      (type-case CLam λ2
                        [(clam l us c)
                         (call-map c
                                   (fst fst-res)
                                   (snd fst-res)
                                   vl)])]
                     [else (error 'call-map "branches must be lambdas")]))])]
             [else (error 'call-map "branches must be lambdas")])]
          [else
           (error 'call-map "Conditional should be a variable in CPS.")])])]
    [(c-call cc)
     (type-case CCall cc
       [(ccall q e l)
        (type-case CExp q
          [(c-lam λ)
           (error 'call-map "Operator must be a variable for continuation call")]
          [(c-var v)
           (letrec ([loop (λ (exps p)
                            (type-case (Listof UExp) exps
                              [(cons e es) (type-case UExp e
                                             [(u-var uv)
                                              (loop es
                                                    (pair (add-ref (fst p)
                                                                   (cons (cvv v)
                                                                         (cons (uvv uv)
                                                                               vl))
                                                                   (cl l))
                                                          (hash-set (snd p)
                                                                    (cl l)
                                                                    (list-to-set vl))))]
                                             [(u-lam λ)
                                              (loop es
                                                    (ulam-map λ
                                                              (add-ref (fst p)
                                                                       (cons (cvv v) vl)
                                                                       (cl l))
                                                              (hash-set (snd p)
                                                                        (cl l)
                                                                        (list-to-set vl))))]
                                             [else
                                              (loop es
                                                    (pair (add-ref (fst p)
                                                                   (cons (cvv v) vl)
                                                                   (cl l))
                                                          (hash-set (snd p)
                                                                    (cl l)
                                                                    (list-to-set vl))))])]
                              [empty p]))])
             (loop e (pair vtr ltv)))])])]))

(add-ref : ((Hashof Var (HashSet Lab)) (Listof Var) Lab -> (Hashof Var (HashSet Lab))))
(define (add-ref vtl vs l)
  (letrec ([loop (λ (vl map)
                   (type-case (Listof Var) vl
                     [(cons x xs)
                      (type-case (Optionof (HashSet Lab)) (hash-ref map x)
                        [(some v) (loop xs (hash-set map x (set-add l v)))]
                        [(none) (loop xs (hash-set map x (set-add l set-empty)))])]
                     [empty map]))])
    (loop vs vtl)))

(uexp-uvar : ((Listof UExp) -> (Listof Var)))
(define (uexp-uvar es)
  (foldr append
         empty
         (map (λ (e)
                (type-case UExp e
                  [(u-var v) (list (uvv v))]
                  [(u-binop op l r) (ubin-uvar l r)]
                  [else empty]))
              es)))

(ubin-uvar : (UExp UExp -> (Listof Var)))
(define (ubin-uvar l r)
  (foldr append
         empty
         (map (λ (e)
                (type-case UExp e
                  [(u-var v) (list (uvv v))]
                  [(u-binop op l r) (ubin-uvar l r)]
                  [else empty]))
              (list l r))))

(define ex6 (ulam (ulab 1)
                  (list (uvar 'x))
                  (cvar 'k1)
                  (c-call (ccall (c-var (cvar 'k1))
                                 (list (u-lam (ulam (ulab 2)
                                                    (list (uvar 'y))
                                                    (cvar 'k2)
                                                    (u-call (ucall (u-var (uvar 'x))
                                                                   (list (u-var (uvar 'y)))
                                                                   (c-lam (clam (clab 3)
                                                                                (list (uvar 'u))
                                                                                (u-call (ucall (u-var (uvar 'x))
                                                                                               (list (u-var (uvar 'u)))
                                                                                               (c-var (cvar 'k2))
                                                                                               (ulab 4)))))
                                                                   (ulab 5))))))
                                 (clab 6)))))


#;(define pr (ulam (ulab 0) (list (uvar 'id)) (cvar 'h)
                 (u-call (ucall (u-var (uvar 'id)) (list (u-num (unum 1)))
                                (c-lam (clam (clab 1)
                                             (list (uvar 'n1))
                                             (u-call (ucall (u-var (uvar 'id))
                                                            (list (u-num (unum 2)))
                                                            (c-lam (clam (clab 2)
                                                                         (list (uvar 'n2))
                                                                         (c-call (ccall (c-var (cvar 'h))
                                                                                        (u-var (uvar 'n2))
                                                                                        (clab 4)))))
                                                            (ulab 5)))))
                                (ulab 6)))))

#;(define in (u-lam (ulam (ulab 3)
                        (list (uvar 'x))
                        (cvar 'k)
                        (c-call (ccall (c-var (cvar 'k))
                                       (u-var (uvar 'x))
                                       (clab 7))))))
