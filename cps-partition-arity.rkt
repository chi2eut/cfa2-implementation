#lang plait

(require "arity-grammar.rkt")

; CPS Partition supporting multiple arity
(define-type Var
  (uvv [var : UVar])
  (cvv [var : CVar]))

(define-type UVar
  (uvar [x : Symbol]))

(define-type CVar
  (cvar [x : Symbol]))

(define-type UNum
  (unum [n : Number]))

(define-type UBool
  (ubool [b : Boolean]))

(define-type Lab
  (ul [lab : ULab])
  (cl [lab : CLab]))

(define-type ULab
  (ulab [x : Number]))

(define-type CLab
  (clab [x : Number]))

(define-type ULam
  (ulam [l : ULab] [u : (Listof UVar)] [k : CVar] [call : Call]))

(define-type CLam
  (clam [γ : CLab] [u : (Listof UVar)] [call : Call]))

(define-type Call
  (u-call [call : UCall])
  (c-call [call : CCall]))

(define-type UCall
  (ucall [f : UExp] [e : (Listof UExp)] [q : CExp] [l : ULab])
  (uif [conditional : UExp] [then : CExp] [else : CExp] [l : ULab]))

(define-type CCall
  (ccall [q : CExp] [e : (Listof UExp)] [γ : CLab]))

(define-type UExp
  (u-lam [lam : ULam])
  (u-var [var : UVar])
  (u-num [num : UNum])
  (u-bool [bool : UBool])
  (u-binop [op : Binop] [lhs : UExp] [rhs : UExp]))

(define-type CExp
  (c-lam [lam : CLam])
  (c-var [var : CVar]))

(define-type Exp
  (uexp [e : UExp])
  (cexp [e : CExp]))

(define-type Program
  (pr [name : UVar] [ulam : ULam]))

#|
(define-type State
  (s-eval [eval : Eval] [label-var : LV])
  (s-apply [apply : Apply] [label-var : LV]))

(define-type State-Type
  (ENTRY) ; UAPPLY
  (CAPPLY) ; CAPPLY
  (INNER-CEVAL) ; CEVAL with lambda
  (CALL) ; UEVAL where continuation is lambda
  (EXIT-CEVAL) ; CEVAL with operator is a variable
  (EXIT-TC))

(define-type Eval
  (eval [call : Call] [stack : Stack] [heap : Heap]))

(define-type Apply
  (uapply [lam : ULam] [d : (Listof UClos)] [heap : Heap])
  (capply [clos : CClos] [d : (Listof UClos)] [stack : Stack] [heap : Heap]))

(define-type Clos
  (ucc [clos : UClos])
  (ccc [clos : CClos]))

(define-type UClos
  (uc [lams : (HashSet ULam)]
      [nums : (Abs-Val UNum)]
      [bools : (Abs-Val UBool)]))

(define-type (Abs-Val 'a)
  (top)
  (bottom)
  (val [v : 'a]))
 
(define-type CClos
  (cclos [lam : CLam])
  (halt))

|#