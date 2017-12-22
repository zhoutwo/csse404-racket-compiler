#lang racket
(require racket/fixnum)
(require "interp.rkt")
(require "utilities.rkt")

(provide r0-passes r1-passes)

(define (flipper e)
  (match e
    [(? fixnum?) e]
    [`(read) `(read)]
    [`(- ,e1) `(- ,(flipper e1))]
    [`(+ ,e1 ,e2) `(+ ,(flipper e2) ,(flipper e1))]
    [`(program ,e) `(program ,(flipper e))]
    ))

(define (pe-neg r)
  (cond [(fixnum? r) (fx- 0 r)]
  [else `(- ,r)]))

(define (pe-add r1 r2)
  (cond [(and (fixnum? r1) (fixnum? r2)) (fx+ r1 r2)]
  [else `(+ ,r1 ,r2)]))

(define (pe-arith e)
  (match e
    [(? fixnum?) e]
    [`(read) `(read)]
    [`(- ,e1) (pe-neg (pe-arith e1))]
    [`(+ ,e1 ,e2) (pe-add (pe-arith e1) (pe-arith e2))]
    [`(program ,e) `(program ,(pe-arith e))]
    ))

(define (find-sym alist var)
  (if (null? alist)
      #f
      (let ([current (car alist)])
        (if (eq? var (car current))
            (cadr current)
            (find-sym (cdr alist) var)))))

(define (uniquify-helper alist)
  (lambda (e)
    (match e
      [(? symbol?) (find-sym alist e)]
      [(? integer?) e]
      [`(let ([,x ,e]) ,body)
              (let ([newsym (gensym)])
                `(let ([,newsym ,((uniquify-helper alist) e)])
                    ,((uniquify-helper (cons (list x newsym) alist)) body)))]
      [`(program ,e)
              `(program ,((uniquify-helper alist) e))]
      [`(,op ,es ...)
              `(,op ,@(map (uniquify-helper alist) es))] )))

(define (uniquify e)
  ((uniquify-helper '()) e))

(define (cleanList alist)
  (if (null? alist) '()
      (if (null? (car alist))
          (cleanList (cdr alist))
          (cons (car alist) (cleanList (cdr alist))))))

(define (replace ls old new)
  (if (null? ls)
      '()
      (if (eq? (car ls) old)
          (cons new (cdr ls))
          (cons (car ls) (replace (cdr ls) old new)))))

(define (apply-to-last ls proc)
  (if (null? ls)
      '()
      (if (null? (cdr ls))
          (list (proc (car ls)))
          (cons (car ls) (apply-to-last (cdr ls) proc)))))

(define (member? ls a)
  (if (null? ls)
      #f
      (or (eq? (car ls) a)
          (member? (cdr ls) a))))

(define (remove-repeated ls)
  (if (null? ls)
      '()
      (let ([cur (car ls)])
        (if (member? (cdr ls) cur)
          (remove-repeated (cdr ls))
          (cons cur (remove-repeated (cdr ls)))))))

(define (flatten-helper alist)
  (lambda (e)
    (match e
      [(? symbol?) (values e '() (cons e alist))]
      [(? integer?) (values e '() alist)]
      [`(let ([,x ,e]) ,body)
          (begin
            (define-values (lastLetSym flattenedLet letAllVars) ((flatten-helper alist) e))
            (define-values (lastBodySym flattenedBody letBodyVars) ((flatten-helper letAllVars) body))
            (values lastBodySym
                      (append flattenedLet `((assign ,x ,lastLetSym)) flattenedBody)
                      (cons x letBodyVars)))]
      [`(program ,e)
              (begin
                (define-values (lastSym flattened allVars) ((flatten-helper alist) e))
                (values
                  '()
                  `(program ,allVars ,@flattened (return ,lastSym))
                  allVars))]
      [`(read)
              (let ([newSym (gensym)])
                (values
                    newSym
                    `((assign ,newSym (read)))
                    (cons newSym alist)))]
      [`(,op ,es ...)
              (begin
                (define-values (lastSym flattened allVars) (map3 (flatten-helper alist) es))
                (let ([newSym (gensym)]
                      [flattened (cleanList flattened)]
                      [allVars (remove-repeated (apply append (cleanList allVars)))])
                  (values newSym
                          (append (apply append flattened) `((assign ,newSym (,op ,@lastSym))))
                          (cons newSym allVars))))
              ])))

(define (flatten e)
  (define-values (a b c) ((flatten-helper '()) e))
  b)

(define (select-instructions e)
  (match e
    [(? symbol?) `((var ,e))]
    [(? integer?) `((int ,e))]
    [`(assign ,lhs (+ ,op1 ,lhs))
            `((addq ,@(select-instructions op1) ,@(select-instructions lhs)))]
    [`(assign ,lhs (+ ,lhs ,op1))
            `((addq ,@(select-instructions op1) ,@(select-instructions lhs)))]
    [`(assign ,lhs (+ ,op1 ,op2))
            `((movq ,@(select-instructions op1) ,@(select-instructions lhs))
              (addq ,@(select-instructions op2) ,@(select-instructions lhs)))]
    [`(assign ,lhs (- ,op1))
            `((movq ,@(select-instructions op1) ,@(select-instructions lhs))
              (negq ,@(select-instructions lhs)))]
    [`(assign ,lhs (read))
            `((callq read_int)
              (movq (reg rax) ,@(select-instructions lhs)))]
    [`(assign ,lhs ,num)
            `((movq ,@(select-instructions num) ,@(select-instructions lhs)))]
    [`(return ,arg)
            `((movq ,@(select-instructions arg) (reg rax)))]
    [`(program ,var ,e ...)
            `(program ,var ,@(apply append (map select-instructions e)))]))

(define (assign-home e)
  (let* ([vars (cadr e)]
        [varlocs (let loop ([varsleft vars]
                      [locs '()]
                      [size 0])
                      (if (null? varsleft)
                          locs
                          (loop (cdr varsleft) (append locs `((,(car varsleft) ,(+ 16 size)))) (+ 16 size))))])
        `(program ,(* 16 (length vars)) ,@(map (assign-home-helper varlocs) (cddr e)))))

(define (assign-home-helper varlocs)
  (lambda (e)
    (match e
      [`(var ,vname)
              `(deref rbp ,(- (car (lookup vname varlocs))))]
      [`(int ,n) e]
      [`(reg ,r) e]
      [`(callq read_int) e]
      [`(negq ,op1)
              (let ([e1 ((assign-home-helper varlocs) op1)])
                `(negq ,e1))]
      [`(,o ,op1 ,op2)
              (let ([e1 ((assign-home-helper varlocs) op1)]
                    [e2 ((assign-home-helper varlocs) op2)])
                    `(,o ,e1 ,e2))])))

(define (patch-instructions e)
  (match e
    [`(program ,var ,e ...)
            `(program ,var ,@(apply append (map patch-instructions e)))]
    [`(movq (deref rbp ,l1) (deref rbp ,l2))
            `((movq (deref rbp ,l1) (reg rax))
              (movq (reg rax) (deref rbp ,l2)))]
    [`(addq (deref rbp ,l1) (deref rbp ,l2))
            `((movq (deref rbp ,l1) (reg rax))
              (addq (reg rax) (deref rbp ,l2)))]
    [else `(,e)]))

(define (print-x86 e)
  (match e
    [`(program ,var ,es ...)
            (let loop ([body (map print-x86 es)]
                        [str (string-append
                              ".global _main\n"
                              "_main:\n"
                              "\tpushq %rbp\n"
                              "\tmovq %rsp, %rbp\n"
                              "\tsubq $"
                              (number->string var)
                              ", %rsp\n")])
                  (if (null? body)
                    (string-append
                      str
                      "\tmovq %rax, %rdi\n"
                      "\tcallq _print_int\n"
                      "\tmovq $0, %rax\n"
                      "\taddq $"
                      (number->string var)
                      ", %rsp\n"
                      "\tpopq %rbp\n"
                      "\tretq\n"
                      )
                    (loop (cdr body) (string-append str (car body))))
              )]
    [`(int ,n)
            (string-append "$" (number->string n))]
    [`(reg ,r)
            (string-append "%" (symbol->string r))]
    [`(callq read_int)
            (string-append "\tcallq _read_int\n")]
    [`(deref ,reg ,dis)
            (string-append
              (number->string dis)
              "(%"
              (symbol->string reg)
              ")")]
    [`(negq ,op1)
            (string-append
              "\tnegq "
              (print-x86 op1)
              "\n")]
    [`(,o ,op1 ,op2)
            (string-append
              "\t"
              (symbol->string o)
              " "
              (print-x86 op1)
              ", "
              (print-x86 op2)
              (string-append "\n"))]))

(define r0-passes
  `(("flipper" ,flipper ,interp-scheme)
     ("partial evaluator" ,pe-arith ,interp-scheme)
     ))

(define r1-passes
  `(("uniquify" ,uniquify ,null)
    ("flatten" ,flatten ,null)
    ("select-instructions" ,select-instructions ,null)
    ("assign-home" ,assign-home ,null)
    ("patch-instructions" ,patch-instructions ,null)
    ("print-x86" ,print-x86 ,interp-x86)
  ))
