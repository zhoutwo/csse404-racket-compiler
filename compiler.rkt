#lang racket
(require racket/fixnum)
(require "interp.rkt")
(require "utilities.rkt")

(provide r0-passes r1-passes r1-with-register-allocation-passes typecheck-R2 r2-passes)

;; Begin R0 compiler

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

;; Beging R1 compiler

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
      [(? boolean?) e]
      [`(let ([,x ,e]) ,body)
              (let ([newsym (gensym)])
                `(let ([,newsym ,((uniquify-helper alist) e)])
                    ,((uniquify-helper (cons (list x newsym) alist)) body)))]
      [`(if ,cond ,thn, alt)
              `(if ,((uniquify-helper alist) cond)
                   ,((uniquify-helper alist) thn)
                   ,((uniquify-helper alist) alt))]
      [`(program (type ,t) ,e)
              `(program (type ,t) ,((uniquify-helper alist) e))]
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
      (or (equal? (car ls) a)
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
      [(? boolean?) (values e '() alist)]
      [`(let ([,x ,e]) ,body)
          (begin
            (define-values (lastLetSym flattenedLet letAllVars) ((flatten-helper alist) e))
            (define-values (lastBodySym flattenedBody letBodyVars) ((flatten-helper letAllVars) body))
            (values lastBodySym
                      (append flattenedLet `((assign ,x ,lastLetSym)) flattenedBody)
                      (cons x letBodyVars)))]
      [`(program (type ,t) ,e)
              (begin
                (define-values (lastSym flattened allVars) ((flatten-helper alist) e))
                (values
                  '()
                  `(program ,(remove-repeated allVars) (type ,t) ,@flattened (return ,lastSym))
                  allVars))]
      [`(program ,e)
              (begin
                (define-values (lastSym flattened allVars) ((flatten-helper alist) e))
                (values
                  '()
                  `(program ,(remove-repeated allVars) ,@flattened (return ,lastSym))
                  allVars))]
      [`(read)
              (let ([newSym (gensym)])
                (values
                    newSym
                    `((assign ,newSym (read)))
                    (cons newSym alist)))]
      [`(if ,cond ,thn ,alt)
              (begin
                (define-values (lastCondSym condFlattened allVars) ((flatten-helper alist) cond))
                (define-values (lastThnSym thnFlattened allVars1) ((flatten-helper allVars) thn))
                (define-values (lastAltSym altFlattened allVars2) ((flatten-helper allVars1) alt))
                (let ([ifSym (gensym)])
                  (values ifSym
                          (append condFlattened
                                  `((if (eq? #t ,lastCondSym)
                                      (,@thnFlattened (assign ,ifSym ,lastThnSym))
                                      (,@altFlattened (assign ,ifSym ,lastAltSym)))))
                          (cons ifSym allVars2))))]
      [`(and ,op1 ,op2)
              ((flatten-helper alist) `(if ,op1 ,op2 #f))]
      [`(,op ,es ...)
              (begin
                (define-values (lastSym flattened allVars) (map3 (flatten-helper alist) es))
                (let ([newSym (gensym)]
                      [flattened (cleanList flattened)]
                      [allVars (remove-repeated (apply append (cleanList allVars)))])
                  (values newSym
                          (append (apply append flattened) `((assign ,newSym (,op ,@lastSym))))
                          (cons newSym allVars))))])))

(define (flatten e)
  (define-values (a b c) ((flatten-helper '()) e))
  b)

(define (select-instructions e)
  (match e
    [(? symbol?) `((var ,e))]
    [(? integer?) `((int ,e))]
    [(? boolean?) (if e
                    `((int 1))
                    `((int 0)))]
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
    [`(assign ,lhs (eq? ,op1 ,op2))
            (let ([op1 (car (select-instructions op1))]
                  [op2 (car (select-instructions op2))]
                  [lhs (car (select-instructions lhs))])
                  `((cmpq ,op2 ,op1)
                    (set e (byte-reg al))
                    (movzbq (byte-reg al) ,lhs)))]
    [`(assign ,lhs (> ,op1 ,op2))
            (let ([op1 (car (select-instructions op1))]
                  [op2 (car (select-instructions op2))]
                  [lhs (car (select-instructions lhs))])
                  `((cmpq ,op2 ,op1)
                    (set g (byte-reg al))
                    (movzbq (byte-reg al) ,lhs)))]
    [`(assign ,lhs (>= ,op1 ,op2))
            (let ([op1 (car (select-instructions op1))]
                  [op2 (car (select-instructions op2))]
                  [lhs (car (select-instructions lhs))])
                  `((cmpq ,op2 ,op1)
                    (set ge (byte-reg al))
                    (movzbq (byte-reg al) ,lhs)))]
    [`(assign ,lhs (<= ,op1 ,op2))
            (let ([op1 (car (select-instructions op1))]
                  [op2 (car (select-instructions op2))]
                  [lhs (car (select-instructions lhs))])
                  `((cmpq ,op2 ,op1)
                    (set le (byte-reg al))
                    (movzbq (byte-reg al) ,lhs)))]
    [`(assign ,lhs (< ,op1 ,op2))
            (let ([op1 (car (select-instructions op1))]
                  [op2 (car (select-instructions op2))]
                  [lhs (car (select-instructions lhs))])
                  `((cmpq ,op2 ,op1)
                    (set l (byte-reg al))
                    (movzbq (byte-reg al) ,lhs)))]
    [`(assign ,lhs (not ,op1))
            (let ([op1 (car (select-instructions op1))]
                  [lhs (car (select-instructions lhs))])
                  `((movq ,op1 (reg rax))
                    (xorq (int 1) (reg rax))
                    (movq (int 1) (reg rbx))
                    (cmpq (reg rbx) (reg rax))
                    (set e (byte-reg al))
                    (movzbq (byte-reg al) ,lhs)))]
    [`(assign ,lhs ,num)
            `((movq ,@(select-instructions num) ,@(select-instructions lhs)))]
    [`(return ,arg)
            `((movq ,@(select-instructions arg) (reg rax)))]
    [`(if ,cond ,thns ,alts)
            `((if (eq? ,@(select-instructions (cadr cond)) ,@(select-instructions (caddr cond)))
                 ,(apply append (map select-instructions thns))
                 ,(apply append (map select-instructions alts))))]
    [`(program ,var (type ,t) ,e ...)
            `(program ,var (type ,t) ,@(apply append (map select-instructions e)))]
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
              (let ([loc (car (lookup vname varlocs))])
                    (if (number? loc)
                      `(deref rbp ,(- loc))
                      `(reg ,loc)))]
      [`(int ,n) e]
      [`(reg ,r) e]
      [`(byte-reg ,r) e]
      [`(callq read_int) e]
      [`(if (eq? ,v1 ,v2) ,thn ,thnlive ,alt ,altlive)
              `(if (eq? ,((assign-home-helper varlocs) v1) ,((assign-home-helper varlocs) v2))
                  ,(map (assign-home-helper varlocs) thn)
                  ,(map (assign-home-helper varlocs) alt))]
      [`(if (eq? ,v1 ,v3) ,thn ,alt)
            (error "shouldnot happen" 1)]
      [`(set ,cc ,var)
              `(set ,cc ,((assign-home-helper varlocs) var))]
      [`(,o ,op1)
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
    [`(program ,var (type ,t) ,e ...)
            `(program ,var (type ,t) ,@(apply append (map patch-instructions e)))]
    [`(movq (deref rbp ,l1) (deref rbp ,l2))
            `((movq (deref rbp ,l1) (reg rax))
              (movq (reg rax) (deref rbp ,l2)))]
    [`(addq (deref rbp ,l1) (deref rbp ,l2))
            `((movq (deref rbp ,l1) (reg rax))
              (addq (reg rax) (deref rbp ,l2)))]
    [`(cmpq ,rest (int ,l2))
            `((movq (int ,l2) (reg rax))
              (cmpq ,rest (reg rax)))]
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

;; Begin R1 compiler with register allocation code
(define (vars-read e)
  (match e
    [`(addq (var ,v1) (var ,v2)) `(,v1 ,v2)]
    [`(addq (var ,v) ,rest) `(,v)]
    [`(addq ,rest (var ,v)) `(,v)]
    [`(cmpq (var ,v1) (var ,v2)) `(,v1 ,v2)]
    [`(cmpq (var ,v) ,rest) `(,v)]
    [`(cmpq ,rest (var ,v)) `(,v)]
    [`(xorq (var ,v1) (var ,v2)) `(,v1 ,v2)]
    [`(xorq (var ,v) ,rest) `(,v)]
    [`(xorq ,rest (var ,v)) `(,v)]
    [`(eq? (var ,v1) (var ,v2)) `(,v1 ,v2)]
    [`(eq? (var ,v) ,rest) `(,v)]
    [`(eq? ,rest (var ,v)) `(,v)]
    [`(> (var ,v1) (var ,v2)) `(,v1 ,v2)]
    [`(> (var ,v) ,rest) `(,v)]
    [`(> ,rest (var ,v)) `(,v)]
    [`(>= (var ,v1) (var ,v2)) `(,v1 ,v2)]
    [`(>= (var ,v) ,rest) `(,v)]
    [`(>= ,rest (var ,v)) `(,v)]
    [`(<= (var ,v1) (var ,v2)) `(,v1 ,v2)]
    [`(<= (var ,v) ,rest) `(,v)]
    [`(<= ,rest (var ,v)) `(,v)]
    [`(< (var ,v1) (var ,v2)) `(,v1 ,v2)]
    [`(< (var ,v) ,rest) `(,v)]
    [`(< ,rest (var ,v)) `(,v)]
    [`(movq (var ,v) ,rest) `(,v)]
    [`(negq (var ,v)) `(,v)]
    [`(eq? (var ,v1) (var ,v2)) `(,v1 ,v2)]
    [`(eq? (var ,v) ,rest) `(,v)]
    [`(eq? ,rest (var ,v)) `(,v)]
    [else '()]))

(define (vars-write e)
  (match e
    [`(addq ,rest (var ,v)) `(,v)]
    [`(cmpq ,rest (var ,v)) `(,v)]
    [`(eq? ,rest (var ,v)) `(,v)]
    [`(> ,rest (var ,v)) `(,v)]
    [`(>= ,rest (var ,v)) `(,v)]
    [`(<= ,rest (var ,v)) `(,v)]
    [`(< ,rest (var ,v)) `(,v)]
    [`(xorq ,rest (var ,v)) `(,v)]
    [`(movq ,rest (var ,v)) `(,v)]
    [`(negq (var ,v)) `(,v)]
    [else '()]))

(define (last ls)
  (if (null? (cdr ls))
    (car ls)
    (last (cdr ls))))

(define (make-before after e ls)
  (let ([W (vars-write e)]
        [R (vars-read e)])
        (set-union (set-subtract after W) R)))

(define (uncover-live-helper e ls)
  (match e
    [`(program ,vars (type ,t) ,es ...)
      (begin
          (define-values (lives ees) (uncover-live-helper es ls))
          `(program (,vars ,(cdr lives) (type ,t)) ,@(reverse ees)))]
    [`(program ,vars ,es ...)
      (begin
          (define-values (lives ees) (uncover-live-helper es ls))
          `(program (,vars ,(cdr lives)) ,@(reverse ees)))]
    [else
      (let loop ([es (reverse e)]
                 [ls ls])
          (if (null? es) (values ls es)
              (match (car es)
                [`(if (eq? ,v1 ,v2) ,thn ,alt)
                    (let-values ([(thnlive thn) (uncover-live-helper thn ls)]
                                  [(altlive alt) (uncover-live-helper alt ls)])
                                  (let ([before (set-union (car thnlive) (car altlive) (vars-read `(eq? ,v1 ,v2)))])
                                      (define-values (lls ees) (loop (cdr es) (cons before ls)))
                                      (values lls (cons `(if (eq? ,v1 ,v2) ,(reverse thn) ,thnlive ,(reverse alt) ,altlive) ees))))]
                [else
                    (let* ([after (car ls)]
                           [before (make-before after (car es) ls)])
                        (define-values (lls ees) (loop (cdr es) (cons before ls)))
                        (values lls (cons (car es) ees)))])))]))

(define (uncover-live e)
  (uncover-live-helper e '(())))

(define (build-interference-helper g afters es)
  (if (null? es)
      g
      (let ([currentA (car afters)]
            [currentE (car es)])
            (match currentE
              [`(if (eq? ,v1 ,v2) ,thn ,thnlive ,alt ,altlive)
                    (begin
                      (build-interference-helper g thnlive thn)
                      (build-interference-helper g altlive alt)
                      (build-interference-helper g (cdr afters) (cdr es)))]
              [`(cmpq (var ,s) (var ,d))
                    (begin
                      (map (lambda (v)
                              (if (and (not (eq? v d)) (not (eq? v s)))
                                  (begin (add-edge g d v) (add-edge g v d))
                                  "Useless value")) currentA)
                      (build-interference-helper g (cdr afters) (cdr es)))]
              [`(cmpq ,rest (var ,d))
                    (begin
                      (map (lambda (v)
                              (if (not (eq? v d))
                                  (begin (add-edge g d v) (add-edge g v d))
                                  "Useless value")) currentA)
                      (build-interference-helper g (cdr afters) (cdr es)))]
              [`(movq (var ,s) (var ,d))
                    (begin
                      (map (lambda (v)
                              (if (and (not (eq? v d)) (not (eq? v s)))
                                  (begin (add-edge g d v) (add-edge g v d))
                                  "Useless value")) currentA)
                      (build-interference-helper g (cdr afters) (cdr es)))]
              [`(movq ,rest (var ,d))
                    (begin
                      (map (lambda (v)
                              (if (not (eq? v d))
                                  (begin (add-edge g d v) (add-edge g v d))
                                  "Useless value")) currentA)
                      (build-interference-helper g (cdr afters) (cdr es)))]
              [`(movzbq (var ,s) (var ,d))
                    (begin
                      (map (lambda (v)
                              (if (and (not (eq? v d)) (not (eq? v s)))
                                  (begin (add-edge g d v) (add-edge g v d))
                                  "Useless value")) currentA)
                      (build-interference-helper g (cdr afters) (cdr es)))]
              [`(movzbq ,rest (var ,d))
                    (begin
                      (map (lambda (v)
                              (if (not (eq? v d))
                                  (begin (add-edge g d v) (add-edge g v d))
                                  "Useless value")) currentA)
                      (build-interference-helper g (cdr afters) (cdr es)))]
              [`(addq ,rest (var ,d))
                    (begin
                      (map (lambda (v)
                              (if (not (eq? v d))
                                  (begin (add-edge g d v) (add-edge g v d))
                                  "Useless value")) currentA)
                      (build-interference-helper g (cdr afters) (cdr es)))]
              [`(eq? ,rest (var ,d))
                    (begin
                      (map (lambda (v)
                              (if (not (eq? v d))
                                  (begin (add-edge g d v) (add-edge g v d))
                                  "Useless value")) currentA)
                      (build-interference-helper g (cdr afters) (cdr es)))]
              [`(> ,rest (var ,d))
                    (begin
                      (map (lambda (v)
                              (if (not (eq? v d))
                                  (begin (add-edge g d v) (add-edge g v d))
                                  "Useless value")) currentA)
                      (build-interference-helper g (cdr afters) (cdr es)))]
              [`(>= ,rest (var ,d))
                    (begin
                      (map (lambda (v)
                              (if (not (eq? v d))
                                  (begin (add-edge g d v) (add-edge g v d))
                                  "Useless value")) currentA)
                      (build-interference-helper g (cdr afters) (cdr es)))]
              [`(<= ,rest (var ,d))
                    (begin
                      (map (lambda (v)
                              (if (not (eq? v d))
                                  (begin (add-edge g d v) (add-edge g v d))
                                  "Useless value")) currentA)
                      (build-interference-helper g (cdr afters) (cdr es)))]

              [`(< ,rest (var ,d))
                    (begin
                      (map (lambda (v)
                              (if (not (eq? v d))
                                  (begin (add-edge g d v) (add-edge g v d))
                                  "Useless value")) currentA)
                      (build-interference-helper g (cdr afters) (cdr es)))]
              [else (build-interference-helper g (cdr afters) (cdr es))]))))

(define (build-interference e)
  (match e
    [`(program (,vars ,afters) ,es ...)
        (let ([g (make-graph vars)])
          (let ([processedG (build-interference-helper g afters es)])
            `(program (,vars ,g) ,@es)))]
    [`(program (,vars ,afters (type ,t)) ,es ...)
        (match (build-interference `(program (,vars ,afters) ,@es))
          [`(program (,vars ,g) ,es ...)
            `(program (,vars ,g (type ,t)) ,@es)])]))

(define (color-graph g vars)
  (let ([rg (make-graph vars)])
    (while (not (null? vars))
      (set! vars (sort vars (lambda (a b)
                              (let ([neighborsA (set->list (adjacent g a))]
                                    [neighborsB (set->list (adjacent g b))])
                                    (let ([countColored (lambda (n)
                                                          (if (null? (adjacent rg n))
                                                              0
                                                              1))])
                                          (let ([countA (apply + (map countColored neighborsA))]
                                                [countB (apply + (map countColored neighborsB))])
                                                (>= countA countB)))))))
      (let ([mostSaturated (car vars)])
        (let ([neighbors (set->list (adjacent g mostSaturated))])
          (let ([lowestColor (let ([neighborColors (map (lambda (n) (if (set-empty? (adjacent rg n))
                                                                          #f
                                                                          (car (set->list (adjacent rg n))))) neighbors)])
            (let loop ([lowestColor 0])
              (if (member? neighborColors lowestColor)
                  (loop (+ 1 lowestColor))
                  lowestColor)))])
            (add-edge rg mostSaturated lowestColor)
            (set! vars (remove mostSaturated vars))))))
    rg))

(define (remove-all ls toRemove)
  (if (null? ls)
      '()
      (let ([cur (car ls)])
        (if (eq? cur toRemove)
          (remove-all (cdr ls) toRemove)
          (cons cur (remove-all (cdr ls) toRemove))))))

(define (allocate-registers-helper e regs)
  (match e
    [`(program (,vars ,g (type ,t)) ,es ...)
        (match (allocate-registers-helper `(program (,vars ,g) ,@es) regs)
          [`(program ,size ,es ...)
              `(program ,size (type ,t) ,@es)])]
    [`(program (,vars ,g) ,es ...)
      (let* ([cg (color-graph g vars)]
             [colors (set->list (list->set (map (lambda (var) (car (set->list (adjacent cg var)))) vars)))])
          (let loop1 ([colors colors]
                      [regs regs]
                      [locs '()])
                (cond
                  [(null? colors)
                    (let* ([varlocs (map (lambda (var)
                                                (let ([color (car (set->list (adjacent cg var)))])
                                                    `(,var ,(car (lookup color locs))))) vars)]
                           [size (if (null? varlocs)
                                      0
                                      (let ([foundSize (car (sort (map (lambda (loc)
                                                  (if (number? (cadr loc))
                                                      (abs (cadr loc))
                                                      -1)) varlocs) >))])
                                                      (if (< foundSize 0)
                                                          0
                                                          foundSize)))]
                           [helper (assign-home-helper varlocs)])
                          `(program ,size ,@(map helper es)))]
                  [(null? regs)
                    (let loop ([cleft colors]
                              [locs locs]
                              [size 0])
                                (if (null? cleft)
                                    (loop1 '() '() locs)
                                    (loop (cdr cleft) (append locs `((,(car cleft) ,(+ 16 size)))) (+ 16 size))))]
                  [else
                    (loop1 (cdr colors) (cdr regs) (append locs `((,(car colors) ,(car regs)))))])))]))

(define (allocate-registers e)
  (allocate-registers-helper e (vector->list registers-for-alloc)))

(define (print-x86-with-call-conventions e)
  (match e
    [`(program ,var ,es ...)
            (let loop ([body (map print-x86-with-call-conventions es)]
                        [str (string-append
                              ".global _main\n"
                              "_main:\n"
                              "\tpushq %rbp\n"
                              "\tpushq %rsp\n"
                              "\tpushq %rbx\n"
                              "\tpushq %r12\n"
                              "\tpushq %r13\n"
                              "\tpushq %r14\n"
                              "\tpushq %r15\n"
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
                      "\tpopq %r15\n"
                      "\tpopq %r14\n"
                      "\tpopq %r13\n"
                      "\tpopq %r12\n"
                      "\tpopq %rbx\n"
                      "\tpopq %rsp\n"
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
            (string-append
              "\tpushq %rdx\n"
              "\tpushq %rcx\n"
              "\tpushq %rsi\n"
              "\tpushq %rdi\n"
              "\tpushq %r8\n"
              "\tpushq %r9\n"
              "\tpushq %r10\n"
              "\tpushq %r11\n"
              "\tcallq _read_int\n"
              "\tpopq %r11\n"
              "\tpopq %r10\n"
              "\tpopq %r9\n"
              "\tpopq %r8\n"
              "\tpopq %rdi\n"
              "\tpopq %rsi\n"
              "\tpopq %rcx\n"
              "\tpopq %rdx\n")]
    [`(deref ,reg ,dis)
            (string-append
              (number->string dis)
              "(%"
              (symbol->string reg)
              ")")]
    [`(negq ,op1)
            (string-append
              "\tnegq "
              (print-x86-with-call-conventions op1)
              "\n")]
    [`(,o ,op1 ,op2)
            (string-append
              "\t"
              (symbol->string o)
              " "
              (print-x86-with-call-conventions op1)
              ", "
              (print-x86-with-call-conventions op2)
              (string-append "\n"))]))

;; Beging R2 compiler
(define (typecheck-R2-helper env)
  (lambda (e)
    (define recur (typecheck-R2-helper env))
    (match e
        [(? fixnum?) 'Integer]
        [(? boolean?) 'Boolean]
        [(? symbol?) (lookup e env)]
        [`(eq? ,i1 ,i2)
            (let ([t1 (recur i1)]
                  [t2 (recur i2)])
                  (if (not (eq? t1 t2))
                      (error `typecheck-R2-helper "eq? shoud have same type of operands: ~a, ~a" i1 i2)
                      'Boolean))]
        [`(< ,i1 ,i2)
            (let ([t1 (recur i1)]
                  [t2 (recur i2)])
                  (if (or (not (eq? t1 'Integer))
                          (not (eq? t2 'Integer)))
                      (error "< expects two Integers" i1 i2)
                      'Boolean))]
        [`(<= ,i1 ,i2)
            (let ([t1 (recur i1)]
                  [t2 (recur i2)])
                  (if (or (not (eq? t1 'Integer))
                          (not (eq? t2 'Integer)))
                      (error "<= expects two Integers" i1 i2)
                      'Boolean))]
        [`(> ,i1 ,i2)
            (let ([t1 (recur i1)]
                  [t2 (recur i2)])
                  (if (or (not (eq? t1 'Integer))
                          (not (eq? t2 'Integer)))
                      (error "> expects two Integers" i1 i2)
                      'Boolean))]
        [`(>= ,i1 ,i2)
            (let ([t1 (recur i1)]
                  [t2 (recur i2)])
                  (if (or (not (eq? t1 'Integer))
                          (not (eq? t2 'Integer)))
                      (error ">= expects two Integers" i1 i2)
                      'Boolean))]
        [`(+ ,i1 ,i2)
            (let ([t1 (recur i1)]
                  [t2 (recur i2)])
                  (if (or (not (eq? t1 'Integer))
                          (not (eq? t2 'Integer)))
                      (error "+ expects two Integers" i1 i2)
                      'Integer))]
        [`(and ,i1 ,i2)
            (let ([t1 (recur i1)]
                  [t2 (recur i2)])
                  (if (or (not (eq? t1 'Boolean))
                          (not (eq? t2 'Boolean)))
                      (error "and expects two Booleans" i1 i2)
                      'Boolean))]
        [`(- ,i)
            (let ([t (recur i)])
                  (if (not (eq? t 'Integer))
                      (error "- expects an Integer" i)
                      'Integer))]
        [`(read) 'Integer]
        [`(let ([,x ,(app recur T)]) ,body)
              (define new-env (cons (cons x T) env))
              ((typecheck-R2-helper new-env) body)]
        [`(if ,(app recur con) ,thn ,alt)
            (if (not (eq? con 'Boolean))
              (error `typecheck-R2-helper "if expects Boolean condition: ~a" con)
              (let ([thnt (recur thn)]
                    [altt (recur alt)])
                    (if (not (eq? thnt altt))
                        (error `typecheck-R2-helper "if shoud have same type of thn and alt clauses: ~a, ~a" thn alt)
                        thnt)))]
        [`(not ,(app (typecheck-R2-helper env) T))
              (match T
                ['Boolean 'Boolean]
                [else (error "'not' expects a Boolean" e)])]
        [`(program ,body)
            (define ty ((typecheck-R2-helper '()) body))
                `(program (type ,ty) ,body)])))

(define (typecheck-R2 e)
  ((typecheck-R2-helper '()) e))

(define (lower-conditionals-helper es ees)
  (if (null? es) ees
    (match es
      [`(program ,size (type ,t) ,es ...)
          (let ([ees (lower-conditionals-helper es ees)])
                `(program ,size (type ,t) ,@ees))]
      [else (let ([e (car es)])
                (match e
                    [`(if (eq? ,v1 ,v2) ,thn ,alt)
                        (let ([thenlabel (gensym)]
                              [endlabel (gensym)])
                              (lower-conditionals-helper (cdr es)
                                    (append ees `((cmpq ,v2 ,v1)
                                                  (jmp-if e ,thenlabel)
                                                  ,@(apply append (map lower-conditionals `(,alt)))
                                                  (jmp ,endlabel)
                                                  (label ,thenlabel)
                                                  ,@(apply append (map lower-conditionals `(,thn)))
                                                  (label ,endlabel)))))]
                    [else (lower-conditionals-helper (cdr es) (append ees `(,e)))]))])))

(define (lower-conditionals e)
  (lower-conditionals-helper e '()))

(define (print-x86-R2 e)
  (match e
    [`(program ,var (type ,t) ,es ...)
            (let loop ([body (map print-x86-R2 es)]
                        [str (string-append
                              ".global _main\n"
                              "_main:\n"
                              "\tpushq %rbp\n"
                              "\tpushq %rsp\n"
                              "\tpushq %rbx\n"
                              "\tpushq %r12\n"
                              "\tpushq %r13\n"
                              "\tpushq %r14\n"
                              "\tpushq %r15\n"
                              "\tmovq %rsp, %rbp\n"
                              "\tsubq $"
                              (number->string var)
                              ", %rsp\n")])
                  (if (null? body)
                    (string-append
                      str
                      "\tmovq %rax, %rdi\n"
                      (match t
                        [`Integer "\tcallq _print_int\n"]
                        [`Boolean "\tcallq _print_bool\n"])
                      "\tmovq $0, %rax\n"
                      "\taddq $"
                      (number->string var)
                      ", %rsp\n"
                      "\tpopq %r15\n"
                      "\tpopq %r14\n"
                      "\tpopq %r13\n"
                      "\tpopq %r12\n"
                      "\tpopq %rbx\n"
                      "\tpopq %rsp\n"
                      "\tpopq %rbp\n"
                      "\tretq\n"
                      )
                    (loop (cdr body) (string-append str (car body))))
              )]
    [`(jmp-if ,cc ,l)
            (string-append "\tj" (symbol->string cc) " " (symbol->string l) "\n")]
    [`(jmp ,label)
            (string-append "\tjmp " (symbol->string label) "\n")]
    [`(byte-reg ,r)
            (string-append "%" (symbol->string r))]
    [`(set ,cc ,reg)
            (string-append "\tset" (symbol->string cc) " " (print-x86-R2 reg)"\n")]
    [`(cmpq ,v1 ,v2)
            (string-append "\tcmpq "
                          (print-x86-R2 v1)
                          ", "
                          (print-x86-R2 v2)
                          "\n")]
    [`(xorq ,v1 ,v2)
            (string-append "\txorq "
                          (print-x86-R2 v1)
                          ", "
                          (print-x86-R2 v2)
                          "\n")]
    [`(label ,l)
            (string-append (symbol->string l) ":\n")]
    [`(int ,n)
            (string-append "$" (number->string n))]
    [`(reg ,r)
            (string-append "%" (symbol->string r))]
    [`(callq read_int)
            (string-append
              "\tpushq %rdx\n"
              "\tpushq %rcx\n"
              "\tpushq %rsi\n"
              "\tpushq %rdi\n"
              "\tpushq %r8\n"
              "\tpushq %r9\n"
              "\tpushq %r10\n"
              "\tpushq %r11\n"
              "\tcallq _read_int\n"
              "\tpopq %r11\n"
              "\tpopq %r10\n"
              "\tpopq %r9\n"
              "\tpopq %r8\n"
              "\tpopq %rdi\n"
              "\tpopq %rsi\n"
              "\tpopq %rcx\n"
              "\tpopq %rdx\n")]
    [`(deref ,reg ,dis)
            (string-append
              (number->string dis)
              "(%"
              (symbol->string reg)
              ")")]
    [`(negq ,op1)
            (string-append
              "\tnegq "
              (print-x86-R2 op1)
              "\n")]
    [`(,o ,op1 ,op2)
            (string-append
              "\t"
              (symbol->string o)
              " "
              (print-x86-R2 op1)
              ", "
              (print-x86-R2 op2)
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

(define r1-with-register-allocation-passes
  `(("uniquify" ,uniquify ,null)
    ("flatten" ,flatten ,null)
    ("select-instructions" ,select-instructions ,null)
    ("uncover-live" ,uncover-live ,null)
    ("build-interference" ,build-interference ,null)
    ("allocate-registers" ,allocate-registers ,null)
    ("patch-instructions" ,patch-instructions ,null)
    ("print-x86-with-call-conventions" ,print-x86-with-call-conventions ,interp-x86)
  ))

(define r2-passes
  `(("uniquify" ,uniquify ,null)
    ("flatten" ,flatten ,null)
    ("select-instructions" ,select-instructions ,null)
    ("uncover-live" ,uncover-live ,null)
    ("build-interference" ,build-interference ,null)
    ("allocate-registers" ,allocate-registers ,null)
    ("lower-conditionals" ,lower-conditionals ,null)
    ("patch-instructions" ,patch-instructions ,null)
    ("print-x86-R2" ,print-x86-R2 ,interp-x86)
  ))
