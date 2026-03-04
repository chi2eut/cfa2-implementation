#lang plait

(define-type Expr
  (t [t : Val])
  (s [s : Comp]))

(define-type Val
  (ref [x : Symbol])
  (lam [x : (Listof Symbol)] [e : Expr])
  (num [n : Number])
  (bool [b : Boolean])
  (binOp [op : Binop] [lhs : Expr] [rhs : Expr]))

(define-type Comp
  (comp [f : Expr] [args : (Listof Expr)])
  (compK [exp : Expr] [cont : Expr])
  (ifC [conditional : Expr] [then : Expr] [else : Expr]))

(define-type Binop
  (plus)
  (minus)
  (mult)
  (div))

(define new-var-k
  (let ([n (box 0)])
    (lambda ()
      (begin
        (set-box! n (add1 (unbox n)))
        (string->symbol (string-append "k" (to-string (unbox n))))))))

(define new-var-t
  (let ([m (box 0)])
    (lambda ()
      (begin
        (set-box! m (add1 (unbox m)))
        (string->symbol (string-append "t" (to-string (unbox m))))))))

(define new-var-x
  (let ([m (box 0)])
    (lambda ()
      (begin
        (set-box! m (add1 (unbox m)))
        (string->symbol (string-append "x" (to-string (unbox m))))))))



(Φ : (Val -> Val))
(define (Φ v)
  (type-case Val v
    [(lam x e) (let ([nv (new-var-k)])
                 (lam x (t (lam (list nv) (s (colon e (ref nv)))))))]
    [else v]))

(colon : (Expr Val -> Comp))
(define (colon e K)
  (type-case Expr e
    [(t t*)
     (comp (t K)
           (list (t (Φ t*))))]
    [(s s*)
     (type-case Comp s*
       [(comp f args)
        (type-case Expr f
          [(t t*) (eval-args (t (Φ t*))
                             args
                             empty
                             K)]
          [(s s*) (colon (s s*)
                         (let ([nx (new-var-x)])
                           (lam (list nx)
                                (s (eval-args (t (ref nx))
                                              args
                                              (list (ref nx))
                                              K)))))])]
       [(ifC c thn els)
        (type-case Expr c
          [(t t*)
           (ifC (t t*)
                (t (lam empty
                        (s (colon thn
                                  K))))
                (t (lam empty
                        (s (colon els
                                  K)))))]
          [(s s*)
           (colon (s s*)
                  (let ([nx (new-var-x)])
                    (lam (list nx)
                         (s (ifC (t (ref nx))
                                 (t (lam empty
                                         (s (colon thn
                                                   K))))
                                 (t (lam empty
                                         (s (colon els
                                                   K)))))))))])]
       [else
        (error 'colon "Should' make it here.")])]))

(eval-args : (Expr (Listof Expr) (Listof Val) Val -> Comp))
(define (eval-args f es args K)
  (type-case (Listof Expr) es
    [(cons x xs)
     (type-case Expr x
       [(t t*)
        (eval-args f
                   xs
                   (push-back args (Φ t*))
                   K)]
       [(s s*)
        (colon (s s*)
               (let ([nx (new-var-x)])
                 (lam (list nx)
                      (s (eval-args f
                                    xs
                                    (push-back args (ref nx))
                                    K)))))])]
    [empty
     (compK (s (comp f
                  (map (λ (v)
                         (t v))
                       args)))
            (t K))]))

(push-back : ((Listof 'a) 'a -> (Listof 'a)))
(define (push-back l e)
  (append l (list e)))

; Examples

(define ex (t (lam (list 'x)
                   (t (lam (list 'y) (s (comp (t (ref 'x))
                                              (list (s (comp (t (ref 'x))
                                                             (list (t (ref 'y)))))))))))))

(define ex1 (t (lam (list 'x)
                   (t (lam (list 'y) (s (comp (t (ref 'x))
                                              (list (s (comp (t (ref 'x))
                                                             (list (t (binOp (plus)
                                                                             (t (num 42))
                                                                             (t (ref 'y)))))))))))))))

#;(define ex2 (s (ifC (s (comp (t (primop (pair?)))
                             (list (t (ref 'l)))))
                    (s (comp (t (primop (+)))
                             (list (t (num 1))
                                   (s (comp (t (ref 'len))
                                            (list (s (comp (t (primop (cdr)))
                                                           (list (t (ref 'l)))))))))))
                    (t (num 0)))))

#;(comp
 (t (ref 'k))
 (list (t (lam '(x)
               (t (lam '(k1)
                       (s
                        (comp (t (ref 'k1))
                              (list (t
                                     (lam '(y)
                                          (t (lam '(k2)
                                                  (s (compK (t (ref 'x))
                                                            (list (t (ref 'y)))
                                                            (t (lam '(x1)
                                                                    (s (compK (t (ref 'x))
                                                                              (list (t (ref 'x1)))
                                                                              (t (ref 'k2)))))))))))))))))))))
