(define (triple [x : Integer]) : (Vector Integer Integer Integer)
  (vector x x x))
(let ([tr (triple 13)])
  (+ (vector-ref tr 0)
     (+ (vector-ref tr 1)
        (+ (vector-ref tr 2) 3))))
