#lang plait

;Set
(define-type-alias (HashSet 'a) (Hashof String 'a))

(set-empty : (HashSet 'a))
(define set-empty
  (hash empty))

(set-add : ('a (HashSet 'a) -> (HashSet 'a)))
(define (set-add s set)
  (hash-set set (to-string s) s))

(set-remove : ('a (HashSet 'a) -> (HashSet 'a)))
(define (set-remove s set)
  (hash-remove set (to-string s)))

(set-contains? : ('a (HashSet 'a) -> Boolean))
(define (set-contains? e set)
  (type-case (Optionof 'a) (hash-ref set (to-string e))
    [(some v) #true]
    [(none) #false]))

(set-size : ((HashSet 'a) -> Number))
(define (set-size set)
  (length (hash-keys set)))

(set-to-list : ((HashSet 'a) -> (Listof 'a)))
(define (set-to-list set)
  (letrec ([loop (λ (s)
                   (type-case (Listof String) s
                     [(cons x xs) (cons (type-case (Optionof 'a) (hash-ref set x)
                                          [(some v) v]
                                          [(none) (error 'set-to-list "Shouldn't be here.")])
                                        (loop xs))]
                     [empty empty]))])
    (loop (hash-keys set))))

(list-to-set : ((Listof 'a) -> (HashSet 'a)))
(define (list-to-set list)
  (letrec ([loop (λ (l s)
                   (type-case (Listof 'a) l
                     [(cons x xs)
                      (loop xs
                            (if (set-contains? x s)
                                s
                                (set-add x s)))]
                     [empty s]))])
    (loop list set-empty)))

(set-join : ((HashSet 'a) (HashSet 'a) -> (HashSet 'a)))
(define (set-join s1 s2)
  (letrec ([loop (λ (joined-set s2-keys)
                   (type-case (Listof String) s2-keys
                     [(cons x xs)
                      (loop
                       (type-case (Optionof 'a) (hash-ref joined-set x)
                         [(some v) joined-set]
                         [(none)
                          (hash-set joined-set
                                    x
                                    (type-case (Optionof 'a) (hash-ref s2 x)
                                      [(some v) v]
                                      [(none) (error 'set-join "shouldn't make it here")]))])
                       xs)]
                     [empty joined-set]))])
    (loop s1 (hash-keys s2))))

(set-tostr : ((HashSet 'a) -> String))
(define (set-tostr s)
  (letrec ([loop (λ (l)
                   (type-case (Listof 'a) l
                     [(cons x xs)
                      (string-append (string-append (to-string x) "\n\n")
                                     (loop xs))]
                     [empty ""]))])
    (loop (set-to-list s))))


(set-pop : ((HashSet 'a) -> ('a * (HashSet 'a))))
(define (set-pop s)
  (type-case (Listof 'a) (set-to-list s)
    [(cons x xs)
     (pair x (set-remove x s))]
    [empty
     (error 'set-pop "Set is empty.")]))


(define (foo l)
  (map (λ (x) (+ (length l) x))
       (list 1 2 3 4 5)))


