#lang plait

(require "HashSet.rkt"
         "arity-grammar.rkt"
         "arity-mapping.rkt"
         "cps-partition-arity.rkt"
         "arity-labeling.rkt")

; Local Domains
(define-type State
  (s-eval [eval : Eval] [label-var : LV])
  (s-apply [apply : Apply] [label-var : LV]))

(state-tostr : (State -> String))
(define (state-tostr s)
  (type-case State s
    [(s-eval e lv)
     (type-case Eval e
       [(eval c s h) (foldr string-append ""
                            (list (to-string c) "\n" (to-string s) "\n" (to-string h)))])]
    [(s-apply a lv)
     (type-case Apply a
       [(uapply l d h) (foldr string-append ""
                             (list (to-string l) "\n" (to-string d) "\n" (to-string h)))]
       [(capply c d s h) (foldr string-append ""
                             (list (to-string c) "\n" (to-string d) "\n" (to-string s) "\n" (to-string h)))])]))

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

(define-type-alias Stack (Listof Binding))

(define-type-alias Heap (Listof Binding))

(define-type Binding
  (bind [var : UVar] [clos : UClos]))

(S? : (Lab UVar LV -> Boolean))
(define (S? l var m)
  (type-case LV m
    [(lv vtr ltv)
     (type-case (Optionof (HashSet Var)) (hash-ref ltv l)
       [(some v) (set-contains? (uvv var) v)]
       [(none) (error 'S? (string-append "No Such Label exists: " (to-string l)))])]))

(s-ref? : (UVar LV -> Boolean))
(define (s-ref? var m)
  (type-case LV m
    [(lv vtr ltv)
     (type-case (Optionof (HashSet Lab)) (hash-ref vtr (uvv var))
       [(some v)
        (letrec ([itr (λ (ls)
                        (type-case (Listof Lab) ls
                          [(cons x xs)
                           (type-case (Optionof (HashSet Var)) (hash-ref ltv x)
                             [(some v) (if (set-contains? (uvv var)
                                                          v)
                                           (itr xs)
                                           #f)]
                             [(none) (error 'S? "Shouldn't make it here.")])]
                          [empty #t]))])
          (itr (set-to-list v)))]
       [(none)
        (error 'S? "Variable not bound")])]))

(Au : (UExp Lab Stack Heap LV -> UClos))
(define (Au e ψ st h m)
  (type-case UExp e
    [(u-lam l) (uc (list-to-set (list l)) (bottom) (bottom))]
    [(u-num n) (uc set-empty (val n) (bottom))]
    [(u-var v) (if (S? ψ v m)
                   (lookup st v)
                   (lookup h v))]
    [(u-bool b) (uc set-empty (bottom) (val b))]
    [(u-binop op l r) (if (num-op? op)
                          (uc set-empty
                              (binop-num-eval op (Au l ψ st h m) (Au r ψ st h m))
                              (bottom))
                          ....)]))

(num-op? : (Binop -> Boolean))
(define (num-op? op)
  (type-case Binop op
    [(plus) #t]
    [(minus) #t]
    [(mult) #t]
    [(div) #t]))

(binop-num-eval : (Binop UClos UClos -> (Abs-Val UNum)))
(define (binop-num-eval op left right)
  (let ([l (uc-nums left)]
        [r (uc-nums right)])
    (cond
      [(or (top? l) (top? r)) (top)]
      [(and (bottom? l) (bottom? r)) (bottom)]
      [(bottom? l) l]
      [(bottom? r) r]
      [else
       (type-case Binop op
         [(plus) (cond
                   [(equal? (unum 0) (val-v l)) r]
                   [(equal? (unum 0) (val-v r)) l]
                   [else (top)])]
         [(minus) (cond
                    [(equal? (unum 0) (val-v l)) (val (unum (* -1 (unum-n (val-v r)))))]
                    [(equal? (unum 0) (val-v r)) l]
                    [else (top)])]
         [(mult) (cond
                   [(or (equal? (unum 0) (val-v l)) (equal? (unum 0) (val-v r))) (val (unum 0))]
                   [(equal? (unum 1) (val-v l)) r]
                   [(equal? (unum 1) (val-v r)) l]
                   [else (top)])]
         [(div) (cond
                  [(equal? (unum 1) (val-v r)) l]
                  [else (top)])])])))

(get-type : (State -> State-Type))
(define (get-type s)
  (type-case State s
    [(s-eval ev lv)
     (type-case Eval ev
       [(eval c s h)
        (type-case Call c
          [(u-call cc)
           (type-case UCall cc
             [(ucall f e q l)
              (type-case CExp q
                [(c-lam l) (CALL)]
                [(c-var v) (EXIT-TC)])]
             [else (CALL)])]
          [(c-call cc)
           (type-case CCall cc
             [(ccall q e l)
              (type-case CExp q
                [(c-lam l) (INNER-CEVAL)]
                [(c-var v) (EXIT-CEVAL)])])])])]
    [(s-apply ap lv)
     (type-case Apply ap
       [(uapply l d h)
        (ENTRY)]
       [(capply c d s h)
        (CAPPLY)])]))

(rm-lv : (State -> State))
(define (rm-lv s)
  (type-case State s
    [(s-eval e m)
     (s-eval e (lv (hash empty) (hash empty)))]
    [(s-apply a m)
     (s-apply a (lv (hash empty) (hash empty)))]))

;Lookup
(lookup : (Stack UVar -> UClos))
(define (lookup tf v)
  (type-case (Listof Binding) tf
    [(cons x xs) (if (equal? (bind-var x) v)
                     (bind-clos x)
                     (lookup xs v))]
    [empty (error 'lookup "No such binding in the stack")]))

(add : (Stack UVar UClos -> Stack))
(define (add tf uv uc)
  (type-case (Listof Binding) tf
    [(cons x xs) (if (equal? (bind-var x) uv)
                     (cons (bind (bind-var x)
                                 uc)
                           xs)
                     (cons x (add xs uv uc)))]
    [empty (list (bind uv uc))]))

(multiple-add : (Stack (Listof UVar) (Listof UClos) -> Stack))
(define (multiple-add tf uvs ucs)
  (if (not (equal? (length uvs)
                   (length ucs)))
      (error 'multiple-add "Arity mismatch.")
      (letrec ([loop (λ (ts tf*)
                       (type-case (Listof Binding) ts
                         [(cons x xs) (loop xs
                                            (add tf* (bind-var x) (bind-clos x)))]
                         [empty tf*]))])
        (loop (map2 (λ (uv uc) (bind uv uc)) uvs ucs)
              tf))))

(collect-heap-var : (LV (Listof UVar) (Listof UClos) -> (Listof Binding)))
(define (collect-heap-var m uvs ucs)
  (filter (λ (t) (not (s-ref? (bind-var t) m)))
          (if (not (equal? (length uvs)
                           (length ucs)))
              (error 'collect-heap-var "Arity mismatch.")
              (map2 (λ (uv uc) (bind uv uc)) uvs ucs))))

;succ
(step : (State -> (HashSet State)))
(define (step s)
  (type-case State s
    [(s-eval e lv)
     (type-case Eval e
       [(eval c s h)
        (type-case Call c
          [(c-call cc) (CEA cc s h lv)]
          [(u-call uc) (UEA uc s h lv)])])]
    [(s-apply a lv)
     (type-case Apply a
       [(uapply l d h) (UAE l d h lv)]
       [(capply cc uc s h) (CAE cc uc s h lv)])]))

(UEA : (UCall Stack Heap LV -> (HashSet State)))
(define (UEA ucl s h lv)
  (type-case UCall ucl
    [(ucall f e q l)
     (let ([d (map (λ (exp)
                     (Au exp (ul l) s h lv))
                   e)])
       (list-to-set (map (λ (u)
                           (s-apply (uapply u
                                            d
                                            h)
                                    lv))
                         (type-case UClos (Au f (ul l) s h lv)
                           [(uc λs ns bs)
                            (set-to-list λs)]))))]
    [(uif c t e l)
     (let ([thn-st (if-branch-state t s h lv)]
           [els-st (if-branch-state t s h lv)])
       (list-to-set (type-case UClos (Au c (ul l) s h lv)
                    [(uc λs ns bs)
                     (type-case (Abs-Val UBool) bs
                       [(top) (list thn-st els-st)]
                       [(bottom) empty]
                       [(val v) (if (ubool-b v)
                                    (list thn-st)
                                    (list els-st))])])))]))

(define (if-branch-state cexp s h lv) 
  (type-case CExp cexp
    [(c-lam λ)
     (type-case CLam λ
       [(clam l u c)
        (s-eval (eval c s h)
                lv)])]
    [(c-var v)
     (error 'UEA "Shouldn't make it here.")]))

(UAE : (ULam (Listof UClos) Heap LV -> (HashSet State)))
(define (UAE l d h lv)
  (list-to-set (list (type-case ULam l
                       [(ulam l u k c)
                        (s-eval (eval c
                                      (multiple-add empty
                                                    u
                                                    d)
                                      (let ([hvs (collect-heap-var lv u d)])
                                        (multiple-add h
                                                    (map bind-var hvs)
                                                    (map bind-clos hvs))))
                                lv)]))))

(CEA : (CCall Stack Heap LV -> (HashSet State)))
(define (CEA c tf h lv)
  (type-case CCall c
    [(ccall q e l)
     (list-to-set (list (s-apply (capply (type-case CExp q
                                           [(c-lam l) (cclos l)]
                                           [(c-var v) (error 'CEA "It should be λ")])
                                         (map (λ (exp)
                                                (Au exp (cl l) tf h lv))
                                              e)
                                         tf
                                         h)
                                 lv)))]))


(CAE : (CClos (Listof UClos) Stack Heap LV -> (HashSet State)))
(define (CAE cc d tf h lv)
  (type-case CClos cc
    [(cclos l)
     (type-case CLam l
       [(clam l u c)
        (list-to-set (list (s-eval (eval c
                                         (multiple-add tf
                                                       u
                                                       d)
                                         (let ([hvs (collect-heap-var lv u d)])
                                           (multiple-add h
                                                         (map bind-var hvs)
                                                         (map bind-clos hvs))))
                                   lv)))])]
    [(halt)
     (error 'CAE "It should be continuation lambda")]))

; Helper Function State Breakdown
(st-ev : (State -> Eval))
(define (st-ev s)
  (type-case State s
    [(s-eval ev lv)
     ev]
    [else (error 'st-ev "Should be Eval")]))

(st-ap : (State -> Apply))
(define (st-ap s)
  (type-case State s
    [(s-apply ap lv)
     ap]
    [else (error 'st-ap "Should be Apply")]))

(get-ucall : (Call -> UCall))
(define (get-ucall c)
  (type-case Call c
    [(u-call uc) uc]
    [else (error 'get-ucall "Should be UCall")]))

(get-ccall : (Call -> CCall))
(define (get-ccall c)
  (type-case Call c
    [(c-call cc) cc]
    [else (error 'get-ucall "Should be UCall")]))

(get-clam : (CExp -> CLam))
(define (get-clam q)
  (type-case CExp q
    [(c-lam l) l]
    [else (error 'get-clam "Should be a λ")]))

;workset algorithm
(define-type Sets
  (sets [Summary : (HashSet Tuple)]
        [Callers : (HashSet Tuple)]
        [TCallers : (HashSet Tuple)]
        [Final : (HashSet State)]
        [Seen : (HashSet Tuple)]
        [W : (HashSet Tuple)]))

(define-type Tuple
  (2-ple [s1 : State] [s2 : State])
  (3-ple [s3 : State] [s4 : State] [s1 : State]))

(define-type Set-Type
  (Summary)
  (Callers)
  (TCallers)
  (Final)
  (Seen)
  (W))

(insert : (Tuple Sets Set-Type -> Sets))
(define (insert tuple ss t)
  (type-case Sets ss
    [(sets s c tc f seen w)
     (type-case Set-Type t
       [(Summary) (sets (set-add tuple s) c tc f seen w)]
       [(Callers) (sets s (set-add tuple c) tc f seen w)]
       [(TCallers) (sets s c (set-add tuple tc) f seen w)]
       [(Final) (error 'insert "Shouldn't be here.")]
       [(Seen) (sets s c tc f (set-add tuple seen) w)]
       [(W) (sets s c tc f seen (set-add tuple w))])]))

(insert-final : (State Sets -> Sets))
(define (insert-final state ss)
  (type-case Sets ss
    [(sets s c tc f seen w)
     (sets s c tc (set-add (rm-lv state) f) seen w)]))

(work-set : (ULam UExp LV -> Sets))
(define (work-set pr input lv)
  (let ([in (s-apply (uapply pr
                             (type-case UExp input
                               [(u-lam l) (list (uc (list-to-set (list l)) (bottom) (bottom)))]
                               [(u-num n) (list (uc set-empty (val n) (bottom)))]
                               [else (error 'init "Variable can't be input")])
                             empty)
                     lv)])
    (letrec ([loop (λ (sts)
                     (if (ws-mt? sts)
                         sts
                         (loop (type-case Sets sts
                           [(sets s c tc f seen w)
                            (let* ([rm (set-pop w)]
                                   [newset (sets s c tc f seen (snd rm))])
                              (type-case Tuple (fst rm)
                                [(2-ple s1 s2)
                                 (let ([type (begin
                                               (display (string-append (to-string (get-type s2)) "\n"))
                                               (display (string-append (state-tostr s2) "\n\n\n"))
                                               (get-type s2))])
                                   (cond
                                     [(or (equal? type (ENTRY))
                                          (equal? type (CAPPLY))
                                          (equal? type (INNER-CEVAL)))
                                      (letrec ([step-loop (λ (ns ss)
                                                            (type-case (Listof State) ns
                                                              [(cons s3 xs)
                                                               (step-loop xs
                                                                          (propogate (2-ple s1
                                                                                            s3)
                                                                                     ss))]
                                                              [empty ss]))])
                                        (step-loop (set-to-list (step s2)) newset))]
                                     [(equal? type (CALL))
                                      (letrec ([step-loop (λ (ns ss)
                                                            (type-case (Listof State) ns
                                                              [(cons s3 xs)
                                                               (letrec ([summary-loop (λ (ts sss)
                                                                                        (type-case (Listof Tuple) ts
                                                                                          [(cons t* ts*)
                                                                                           (type-case Tuple t*
                                                                                             [(2-ple s3 s4)
                                                                                              (summary-loop ts*
                                                                                                            (update s1
                                                                                                                    s2
                                                                                                                    s3
                                                                                                                    s4
                                                                                                                    sss
                                                                                                                    lv))]
                                                                                             [else (error 'work-set "It needs to be 2-ple")])]
                                                                                          [empty sss]))])
                                                                 (step-loop xs
                                                                            (let ([r (insert (3-ple s1 s2 s3)
                                                                                             (propogate (2-ple s3 s3)
                                                                                                        ss)
                                                                                             (Callers))])
                                                                              (summary-loop (filter (λ (t)
                                                                                                      (type-case Tuple t
                                                                                                        [(2-ple s s4)
                                                                                                         (equal? s s3)]
                                                                                                        [else #f]))
                                                                                                    (set-to-list (sets-Summary r)))
                                                                                            r))))]
                                                              [empty ss]))])
                                        (step-loop (set-to-list (step s2)) newset))]
                                     [(equal? type (EXIT-CEVAL))
                                      (if (equal? s1 in)
                                          (loop (final s2 newset lv))
                                          (letrec ([up-loop (λ (ts ns)
                                                              (type-case (Listof Tuple) ts
                                                                [(cons t* ts*)
                                                                 (up-loop ts*
                                                                          (type-case Tuple t*
                                                                            [(3-ple s3 s4 s1) (update s3
                                                                                                      s4
                                                                                                      s1
                                                                                                      s2
                                                                                                      ns
                                                                                                      lv)]
                                                                            [else (error 'work-set "It needs to be 2-ple")]))]
                                                                [empty ns]))]
                                                   [pr-loop (λ (ts ns)
                                                              (type-case (Listof Tuple) ts
                                                                [(cons t* ts*)
                                                                 (pr-loop ts*
                                                                          (type-case Tuple t*
                                                                            [(3-ple s3 s4 s1) (propogate (2-ple s3 s2) ns)]
                                                                            [else (error 'work-set "It needs to be 2-ple")]))]
                                                                [empty ns]))])
                                            (let ([r0 (insert (2-ple s1 s2)
                                                              newset
                                                              (Summary))])
                                              (let ([r1 (up-loop (filter (λ (t)
                                                                           (type-case Tuple t
                                                                             [(3-ple s3 s4 s)
                                                                              (equal? s s1)]
                                                                             [else
                                                                              #f]))
                                                                         (set-to-list (sets-Callers r0)))
                                                                 r0)])
                                                (pr-loop (filter (λ (t)
                                                                         (type-case Tuple t
                                                                           [(3-ple s3 s4 s)
                                                                            (equal? s s1)]
                                                                           [else
                                                                            #f]))
                                                                       (set-to-list (sets-TCallers r1)))
                                                               r1)))))]
                                     [(equal? type (EXIT-TC))
                                      (letrec ([loop1 (λ (ss ns)
                                                        (type-case (Listof State) ss
                                                          [(cons s3 xs)
                                                           (loop1 xs
                                                                  (let ([r (insert (3-ple s1 s2 s3)
                                                                                   (propogate (2-ple s3 s3)
                                                                                              ns)
                                                                                   (TCallers))])
                                                                    (letrec ([loop2 (λ (ts nss)
                                                                                      (type-case (Listof Tuple) ts
                                                                                        [(cons x xs)
                                                                                         (type-case Tuple x
                                                                                           [(2-ple s3 s4)
                                                                                            (loop2 xs
                                                                                                   (propogate (2-ple s1 s3)
                                                                                                              nss))]
                                                                                           [else (error 'work-set "It needs to be 3-ple")])]
                                                                                        [empty nss]))])
                                                                      (loop2 (filter (λ (t)
                                                                                       (type-case Tuple t
                                                                                         [(2-ple s s4)
                                                                                          (equal? s s3)]
                                                                                         [else
                                                                                          #f]))
                                                                                     (set-to-list (sets-Summary r)))
                                                                             r))))]
                                                          [empty ns]))])
                                        (loop1 (set-to-list (step s2))
                                                     newset))]))]
                                [else
                                 (error 'work-set "It should be (s1, s2)")]))]))))])
      (loop (sets set-empty
                  set-empty
                  set-empty
                  set-empty
                  (list-to-set (list (2-ple in in)))
                  (list-to-set (list (2-ple in in))))))))

(ws-mt? : (Sets -> Boolean))
(define (ws-mt? sts)
  (type-case Sets sts
    [(sets s c tc f seen w)
     (if (equal? (set-size w)
                 0)
         #t
         #f)]))

(propogate : (Tuple Sets -> Sets))
(define (propogate tuple sts)
  (type-case Sets sts
    [(sets s c tc f seen w)
     (if (not (set-contains? tuple seen))
         (insert tuple
                 (insert tuple
                         sts
                         (Seen))
                 (W))
         sts)]))

(update : (State State State State Sets LV -> Sets))
(define (update s1 s2 s3 s4 sts lv)
  (type-case Apply (st-ap s1)
    [(uapply λ1 d1 h1)
     (type-case ULam λ1
       [(ulam l1 u1 k1 call1)
        (type-case Eval (st-ev s2)
          [(eval c2 tf2 h2)
           (type-case UCall (get-ucall c2)
             [(ucall f e2 q2 l2)
              (type-case CLam (get-clam q2)
                [(clam γ2 u2 call2)
                 (type-case Apply (st-ap s3)
                   [(uapply λ3 d3 h3)
                    (type-case ULam λ3
                      [(ulam l3 u3 k3 call3)
                       (type-case Eval (st-ev s4)
                         [(eval c4 tf4 h4)
                          (type-case CCall (get-ccall c4)
                            [(ccall k4 e4 γ4)
                             (propogate (2-ple s1
                                               (s-apply (capply (cclos (clam γ2
                                                                             u2
                                                                             call2))
                                                                (map (λ (exp)
                                                                       (Au exp
                                                                           (cl γ4)
                                                                           tf4
                                                                           h4
                                                                           lv))
                                                                     e4)
                                                                (type-case UExp f
                                                                  [(u-var v) (cond
                                                                               [(S? (ul l2)
                                                                                    v
                                                                                    lv)
                                                                                (add tf2
                                                                                          v
                                                                                          (uc (list-to-set (list (ulam l3
                                                                                                                       u3
                                                                                                                       k3
                                                                                                                       call3)))
                                                                                              (bottom)
                                                                                              (bottom)))]
                                                                               [else tf2])]
                                                                  [else tf2])
                                                                h4)
                                                        lv))
                                        sts)])])])]
                   [else (error 'update "Should be UApply")])])]
             [(uif c t e l) (error 'update "Shouldn't be an if form")])])])]
    [else (error 'update "Should be UApply")]))

(final : (State Sets LV -> Sets))
(define (final state sets lv)
  (type-case State state
    [(s-eval ev lv)
     (type-case Eval ev
       [(eval c tf h)
        (type-case Call c
          [(c-call cc)
           (type-case CCall cc
             [(ccall k e l)
              (insert-final (s-apply (capply (halt)
                                             (map (λ (exp)
                                                    (Au exp
                                                        (cl l)
                                                        tf
                                                        h
                                                        lv))
                                                  e)
                                             empty
                                             h)
                                     lv)
                            sets)])]
          [else (error 'final "Shouldn't make it here.")])])]
    [else (error 'final "Shouldn't make it here.")]))

(define (run pr in)
  (work-set pr in (gen-map pr in)))

(define sample-pr (ulam (ulab 0) (list (uvar 'id)) (cvar 'h)
                        (u-call (ucall (u-var (uvar 'id)) (list (u-num (unum 1)))
                                       (c-lam (clam (clab 1)
                                                    (list (uvar 'u))
                                                    (u-call (ucall (u-var (uvar 'id))
                                                                   (list (u-num (unum 2)))
                                                                   (c-var (cvar 'h))
                                                                   (ulab 5)))))
                                       (ulab 6)))))


(define pr2 (ulam (ulab 0) (list (uvar 'id)) (cvar 'h)
                        (u-call (ucall (u-var (uvar 'id)) (list (u-num (unum 1)))
                                       (c-lam (clam (clab 1)
                                                    (list (uvar 'n1))
                                                    (u-call (ucall (u-var (uvar 'id))
                                                                   (list (u-num (unum 2)))
                                                                   (c-lam (clam (clab 2)
                                                                                (list (uvar 'n2))
                                                                                (c-call (ccall (c-var (cvar 'h))
                                                                                               (list (u-var (uvar 'n2)))
                                                                                               (clab 4)))))
                                                                   (ulab 5)))))
                                       (ulab 6)))))

(define input (u-lam (ulam (ulab 3)
                           (list (uvar 'x))
                           (cvar 'k)
                           (c-call (ccall (c-var (cvar 'k))
                                          (list (u-var (uvar 'x)))
                                          (clab 7))))))

(define in2 (u-lam (ulam (ulab 3)
                           (list (uvar 'x))
                           (cvar 'k)
                           (c-call (ccall (c-var (cvar 'k))
                                          (list (u-binop (plus) (u-num (unum 1)) (u-var (uvar 'x))))
                                          (clab 7))))))