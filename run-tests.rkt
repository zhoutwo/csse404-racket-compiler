#! /usr/bin/env racket
#lang racket
(require "utilities.rkt")
(require "interp.rkt")
(require "compiler.rkt")

(define make-list
  (lambda (n)
    (if (= 0 n) '()
                (append (make-list (- n 1)) (list n)))))

(debug-level 4)

;(compiler-tests "compiler.rkt" (lambda (e) '()) r1-passes "r1" (make-list 48))
;(compiler-tests "compiler.rkt" (lambda (e) '()) r1-passes "r1a" (make-list 8))

(compiler-tests "compiler.rkt" (lambda (e) '()) r1-with-register-allocation-passes "r1" (make-list 48))
(compiler-tests "compiler.rkt" (lambda (e) '()) r1-with-register-allocation-passes "r1a" (make-list 8))
(newline) (display "tests passed!") (newline)
