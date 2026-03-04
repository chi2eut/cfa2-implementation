#lang plait

(require "arity-grammar.rkt"
         "cps-partition-arity.rkt")

(ulam-label : (Expr -> ULam))
(define (ulam-label e)
  (type-case Expr e
    [(t t*)
     (type-case Val t*
       [(lam xs e)
        (type-case Expr e
          [(t t*)
           (type-case Val t*
             [(lam xs* e*) (ulam (ulab (new-var))
                                 (map (λ (x) (uvar x)) xs)
                                 (cvar (first xs*))
                                 (call-label e*))]
             [else (error 'ulam-label "Should be a lambda")])]
          [(s s*) (error 'ulam-label "Should be lambda")])]
       [else
        (error 'ulam-label "Should be lambda")])]
    [(s s*)
     (error 'ulam-label "comp not allowed.")]))

(clam-label : (Expr -> CLam))
(define (clam-label e)
  (type-case Expr e
    [(t t*)
     (type-case Val t*
       [(lam xs e)
        (clam (clab (new-var))
              (map (λ (x) (uvar x)) xs)
              (call-label e))]
       [else
        (error 'clam-label "Comp not allowed.")])]
    [(s s*)
     (error 'clam-label "Comp not allowed.")]))

(call-label : (Expr -> Call))
(define (call-label e)
  (type-case Expr e
    [(t t*)
     (error 'call-label "Var/Lam not allowed")]
    [(s s*)
     (type-case Comp s*
       [(comp f args)
        (c-call (ccall (cexp-label f)
                       (map (λ (x) (uexp-label x)) args)
                       (clab (new-var))))]
       [(compK app k)
        (type-case Expr app
          [(s s*)
           (type-case Comp s*
             [(comp f args)
              (u-call (ucall (uexp-label f)
                       (map (λ (x) (uexp-label x)) args)
                       (cexp-label k)
                       (ulab (new-var))))]
             [else (error 'call-label "It should be a app")])]
          [else (error 'call-label "It should be a comp")])]
       [(ifC c t e)
        (u-call (uif (uexp-label c)
                     (cexp-label t)
                     (cexp-label e)
                     (ulab (new-var))))])]))

(uexp-label : (Expr -> UExp))
(define (uexp-label e)
  (type-case Expr e
    [(t t*)
     (type-case Val t*
       [(ref x) (u-var (uvar x))]
       [(lam xs e*) (u-lam (ulam-label e))]
       [(num n) (u-num (unum n))]
       [(bool b) (u-bool (ubool b))]
       [(binOp op l r) (u-binop op (uexp-label l) (uexp-label r))])]
    [else (error 'uexp-label "Computation not allowed")]))

(cexp-label : (Expr -> CExp))
(define (cexp-label e)
  (type-case Expr e
    [(t t*)
     (type-case Val t*
       [(ref x) (c-var (cvar x))]
       [(lam xs e*) (c-lam (clam-label e))]
       [else (error 'cexp-label "Not allowed.")])]
    [(s s*)
     (error 'cexp-label "Comp not allowed")]))

(define new-var
  (let ([n (box 0)])
    (lambda ()
      (begin
        (set-box! n (add1 (unbox n)))
        (unbox n)))))