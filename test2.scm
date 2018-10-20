;;normal evaluation
(define num1 1)
(define num2 2)
(define (plus a b) (+ a b))
(define num3 (plus num1 num2))
;;delay test
(define (try a (delayed b)) (if (= a 0) a b))
(display num3)
(display (try 0 (/ 1 0)))

;;reference test
(define u 3)
(define x 10)
(define t 2)
(define g (lambda ((reference x))(f x x) t))
(define f (lambda ((reference x)(reference y))
            (set! x 5) y))
(display (f u u))
(display (f x x))
(display (g t))

;;dynamic test
(define f (lambda(x)(lambda(y)(cons (g x) y))))
(define g (lambda((dynamic z))(cons z 4)))
(define h (f 2))
(define x 1)
(display (h 5))
