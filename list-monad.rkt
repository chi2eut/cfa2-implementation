#lang plait

(concat-map : (('a -> (Listof 'b)) (Listof 'a)  -> (Listof 'b)))
(define (concat-map f m)
  (foldr append empty (map f m)))

(list-bind : ((Listof 'a) ('a -> (Listof 'b)) -> (Listof 'b)))
(define (list-bind m f)
  (concat-map f m))

(list-return : ('a -> (Listof 'a)))
(define (list-return x)
  (list x))

(list-fail : ('a -> (Listof 'a)))
(define (list-fail x)
  empty)

(list-bind (list 1 2 3 4)
           (λ (x)
             (list-bind (list (* x 10) (* x 10))
                        (λ (y)
                          (list-return (* y 100))))))

(run : (((Listof 'a) -> (Listof 'b)) (Listof 'a) -> (Listof 'b)))
(define (run f l)
  (f l))