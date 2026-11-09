#lang racket

(require "../chez-init.rkt")
(require racket/trace)
(provide eval-one-exp)

(provide add-macro-interpreter)
(define add-macro-interpreter (lambda x (error "nyi")))
(provide quasiquote-enabled?)
(define quasiquote-enabled?
         (lambda () (error "nyi"))) ; make this return 'yes if you're trying quasiquote

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

; parsed expression.  You'll probably want to replace this 
; code with your expression datatype from A11b

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp
   (data literal?)]
  [quote-exp
   (data list?)]
  [vec-exp
   (vec vector?)]
  [lambda-exp
   (id expression?)
   (body (listof expression?))]
  [multi-lambda-exp
   (params (listof expression?))
   (body (listof expression?))]
  [app-exp
   (rator expression?)
   (rand (listof expression?))]
  [if-exp
   (test expression?)
   (then expression?)
   (else expression?)]
  [cond-exp
   (exps (listof expression?))]
  [one-arm-if-exp
   (test expression?)
   (then expression?)]
  [normal-let-exp
   (let-type symbol?)
   (vars (listof expression?))
   (exps (listof expression?))
   (body (listof expression?))]
  [set-bang-exp
   (var expression?)
   (body expression?)]
  [and-exp
   (exps (listof expression?))]
  [or-exp
   (exps (listof expression?))]
  [begin-exp
    (exps (listof expression?))]
  [multi-exp
    (exps (listof expression?))]
  )

(define literal?
  (lambda (x)
    (ormap (lambda (pred) (pred x)) (list boolean? vector? number? symbol? string? null?))
    ))
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals (list-of? scheme-value?))
   (env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
   (ids (listof symbol?))
   (bodies (listof expression?))
   (env environment?)]
  [single-closure
   (id symbol?)
   (bodies (listof expression?))
   (env environment?)]
  )

  
;-------------------+
;                   |
;    sec:PARSER     |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Helper procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

; Again, you'll probably want to use your code from A11b

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
      ;[(vector? datum) (vec-exp datum)]
      [(and (pair? datum) (eqv? 'quote (car datum))) (quote-exp (cdr datum))]
      [(literal? datum) (lit-exp datum)]      
      #|[(boolean? datum) (bool-exp datum)]
      [(string? datum) (str-exp datum)]
      |#
      [(pair? datum)
       (cond
         [(eqv? (car datum) 'lambda)
          #| LAMBDA COND |#
          (cond [(< (length datum) 3) (error 'parse-exp "bad lambda expression, too short: ~s" datum)]
                [(list? (2nd datum))
                   (if (= (length (filter symbol? (2nd datum))) (length (2nd datum)))
                       (multi-lambda-exp (map parse-exp (2nd datum)) (map parse-exp (cddr datum)))
                       (error 'parse-exp "bad lambda expression invalid lambda params: ~s" datum) ; lambda params have at least one non symbol
                       )]
                [else (lambda-exp (parse-exp (2nd  datum)) (map parse-exp (cddr datum)))])]
         
         [(eqv? (car datum) 'if)
          #| IF COND |#
          (cond [(= (length datum) 3) (one-arm-if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))]
                [(not (= (length datum) 4))  (error 'parse-exp "bad if expression: ~s" datum)]
                [else (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (4th datum)))])]
         
         [(or (eqv? (car datum) 'let) (eqv? (car datum) 'let*) (eqv? (car datum) 'letrec))
          #| LET COND |#
          (cond [(not (list? (2nd datum))) (error 'parse-exp "bad let expression, vars not a list: ~s" datum)]
                [(not (andmap (lambda (lst) (list? lst)) (2nd datum))) (error 'parse-exp "invalid parameters for let variant")]
                [(not (andmap (lambda (lst) (= (length lst) 2)) (2nd datum))) (error 'parse-exp "bad let-variant expression, vars and vals are not pairs of 2: ~s" datum)]
                ;[(not (andmap (lambda (lst) (= (length lst) 2)) (2nd datum))) (error 'parse-exp "bad let-variant expression, vars and vals are not pairs of 2: ~s" datum)]
                [(not (andmap (lambda (lst) (symbol? (first lst))) (2nd datum))) (error 'parse-exp "local variable inside of let is not a symbol")]
                [(< (length datum) 3) (error 'parse-exp "let expression is too short")]
                [else (normal-let-exp (1st datum)
                                      (map (lambda (fir) (parse-exp (1st fir))) (2nd datum))
                                      (map (lambda (sec) (parse-exp (2nd sec))) (2nd datum))
                                      (map parse-exp (cddr datum)))])]

         [(eqv? (car datum) 'set!)
          (cond [(not (= (length datum) 3)) (error 'parse-exp "bad expression: ~s" datum)]
                [else (set-bang-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))])]
         [(eqv? (car datum) 'and) (and-exp (map parse-exp (cdr datum)))]
         [(eqv? (car datum) 'or) (or-exp (map parse-exp (cdr datum)))]
         [(eqv? (car datum) 'cond) (cond-exp (map parse-exp (cdr datum)))]
         [(eqv? (car datum) 'begin) (begin-exp (map parse-exp (cdr datum)))]
          
         [else (if (list? datum)
                   (app-exp (parse-exp (1st datum))
                        (map parse-exp (cdr datum)))
                   ; not a list, invalid exp 
                   (error 'parse-exp "bad expression: ~s" datum))])]
         
      [else (error 'parse-exp "bad expression: ~s" datum)])))


;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+


; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
            [(eq? sym (car los)) pos]
            [else (loop (cdr los) (add1 pos))]))))

(define apply-env
  (lambda (env sym) 
    (cases environment env 
      [empty-env-record ()      
                        (apply-env-global init-env sym)]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env env sym)))])))

(define apply-env-global
  (lambda (env sym) 
    (cases environment env 
      [empty-env-record ()      
                        (error 'env "variable ~s not found." sym)]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env-global env sym)))])))

#|(define apply-env
  (lambda (env sym) 
    (cases environment env 
      [empty-env-record ()      
                        (error 'env "variable ~s not found." sym)]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env env sym)))])))|#


;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

(define syntax-expand
    (lambda (exp)
        (cases expression exp
            [var-exp (symbol) exp] ;; do nothing
            [lit-exp (literal) exp] ;; do nothing
            [multi-exp (exps) exp]
            [and-exp (exps)
                    (cond [(null? exps) (lit-exp #t)]
                          [(null? (cdr exps)) (syntax-expand (car exps))]
                          [else (if-exp (syntax-expand (car exps))
                                        (syntax-expand (and-exp (cdr exps)))
                                        (lit-exp #f))])]
            [or-exp (exps)
                    (cond [(null? exps) (lit-exp #f)]
                          [(null? (cdr exps)) (syntax-expand (car exps))]
                          [else (if-exp (syntax-expand (car exps))
                                        (car exps)
                                        (syntax-expand (or-exp (cdr exps)))
                                        )])]
          [begin-exp (exps) (cond [(null? (cdr exps)) (syntax-expand (car exps))]
                                  [else (multi-exp (list (syntax-expand (car exps)) (syntax-expand (begin-exp (cdr exps)))))])]
          [cond-exp (exps)
                    ;(display exps)
                   ; (newline)
                  ;  (newline)
                   ;(display (cdr (car exps)))
                    (cond 
                          [(null? (cdr exps))
                           (if (eqv? (2nd (2nd (car exps))) 'else)
                               (syntax-expand (1st (3rd (1st exps))))
                               (one-arm-if-exp (syntax-expand (cadar exps))
                                               (syntax-expand (car (cadr (cdr (car exps)))))
                                               )
                               )]
                          ;[(eqv? (1st exp) 'else) (syntax-expand (cdr (car exps)))]
                          [else ;(begin (display "cdr exps:" cddr exps)(newline)
                                       (if-exp (syntax-expand (cadar exps))
                                        ;(one-arm-if-exp (syntax-expand (cadar exps))
                                                        (syntax-expand (car (cadr (cdr (car exps)))))
                                         ;               )
                                        (syntax-expand (cond-exp (cdr exps))))]
                          )]
            [normal-let-exp (let-type vars exps body)
                            (cond [(equal? let-type 'let)
                                   (normal-let-exp let-type
                                                   (map syntax-expand vars)
                                                   (map syntax-expand exps)
                                                   (map syntax-expand body))]
                                  [(equal? let-type 'let*)
                                   (if (null? (cdr exps))
                                       (normal-let-exp 'let
                                                   (list (syntax-expand (car vars)))
                                                   (list (syntax-expand (car exps)))
                                                   (map syntax-expand body))
                                       (normal-let-exp 'let
                                                   (list (syntax-expand (car vars)))
                                                   (list (syntax-expand (car exps)))
                                                   (list (syntax-expand (normal-let-exp 'let* (cdr vars) (cdr exps) body)))))])]
                      
          
          
      [quote-exp (datum) exp]
      [one-arm-if-exp (test then) (one-arm-if-exp (syntax-expand test)
                                                 (syntax-expand then))] ; will need fixed
      [if-exp (test then else) (if-exp (syntax-expand test)
                                       (syntax-expand then)
                                       (syntax-expand else))]       
      [multi-lambda-exp (params body) exp]
      [lambda-exp (id body) exp]
      [vec-exp (datum) datum]
      [app-exp (rator rands) exp]
      [set-bang-exp (var body) exp]
       
          )))
          
    ;; so many more cases go here

;---------------------------------------+
;                                       |
; sec:CONTINUATION DATATYPE and APPLY-K |
;                                       |
;---------------------------------------+

; To be added in assignment 18a.


;-------------------+
;                   |
;  sec:INTERPRETER  |
;                   |
;-------------------+

; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp (empty-env) form)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (env exp)
   #| (display env)
    (newline)
    (display exp)
    (newline) |#
    ;(display exp)
    ;(newline)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
               (apply-env env id)]
      [quote-exp (datum)
                 (car datum)]
      [begin-exp (exps)
                 (eval-bodies env exps)]
      [multi-exp (exps)
                 (car (reverse (map (lambda (x)
                        (eval-exp env x)) exps)))]
      [one-arm-if-exp (test then)
              (when (eval-exp env test)
                  (eval-exp env then))]
      [if-exp (test then else)
              (if (eval-exp env test)
                  (eval-exp env then)
                  (eval-exp env else))]
      [normal-let-exp (let-type vars exps body)
                      (eval-bodies (extend-env (map (lambda (e2) (2nd e2)) vars)
                                               (eval-expressions env exps) env) body)]
                     #| (let* ([init-vals (eval-rands env exps)]
                             [init-vars (eval-rators vars)]
                      [new-env (extend-env
                                init-vars
                                init-vals
                                env)])
                      (last (eval-rands new-env body)))] |#
                   
      [multi-lambda-exp (params body)
                        (closure (map (lambda (e2) (2nd e2)) params) body env)]
      [lambda-exp (id body)
                  (single-closure (2nd id) body env)]
      ;[multi-lambda-exp (params bodies)
       ;           (closure (map (lambda (e2)(2nd e2)) params) bodies env)]
      [vec-exp (datum) datum]
      [app-exp (rator rands)
               (let ([proc-value (eval-exp env rator)]
                     [args (eval-expressions env rands)])
                 (begin  (newline)  (newline) (apply-proc proc-value args)))]
      [else (error 'eval-exp "Bad abstract syntax: ~a ~a" exp env)])))

; evaluate the list of operands, putting results into a list

(define eval-bodies
  (lambda (env bodies)
    (if (null? (cdr bodies))
        (eval-exp env (car bodies))
        (begin
          (eval-exp env (car bodies))
          (eval-bodies env (cdr bodies))))
))

(define eval-expressions
  (lambda (env rands)
    (map ((curry eval-exp) env) rands)))

(define eval-rands
  (lambda (env rands)
    (map (lambda (exp) (eval-exp env exp)) rands)))

(define eval-rators
  (lambda (rators)
    (map (lambda (exp) (cadr exp)) rators)))

(define eval-params
  (lambda (params)
    (map (lambda (exp) (cadr exp)) params)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [single-closure (id bodies env)
                      (eval-bodies (extend-env (list id) (list args) env) bodies)]
      [closure (ids bodies env) (eval-bodies (extend-env ids args env) bodies)]
      ; You will add other cases
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 cons car =
                              zero? not <= >= < > cdr list null?
                              assq eq? equal? atom? length list->vector list?
                              pair? procedure? vector->list vector make-vector
                              vector-ref vector? number? symbol? vector-set!
                             display newline cadr caar cadar caadr caaadr caaaadr caddr
                              cadddr caddddr map apply))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
   *prim-proc-names*   ;  a value (not an expression) with an identifier.
   (map prim-proc      
        *prim-proc-names*)
   (empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(null?) (null? (car args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(list) (apply list args)]
      [(list?) (list? (car args))]
      [(pair?) (pair? (car args))]
      [(length) (length (car args))]
      [(cons) (cons (1st args) (2nd args))]
      [(car) (car (car args))]
      [(caar) (caar (car args))]
      [(cadr) (cadr (car args))]
      [(cadar) (cadar (car args))]
      [(cdr) (cdr (car args))]
      [(not) (not (car args))]
      [(zero?) (zero? (car args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [(>) (> (1st args) (2nd args))]
      [(>=) (>= (1st args) (2nd args))]
      [(<=) (<= (1st args) (2nd args))]
      [(<) (< (1st args) (2nd args))]
      [(vector) (apply vector args)]
      [(vector->list) (vector->list (1st args))]
      [(list->vector) (list->vector (1st args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector?) (vector? (1st args))]
      [(number?) (number? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(procedure?) (proc-val? (1st args))]
      [(map) (map (lambda (x) (apply-proc (1st args) (list x))) (2nd args))]
      [(apply) (apply-proc (1st args) (2nd args))]
      ;[(apply) (apply (1st args) (2nd args))]
      [else (error 'apply-prim-proc 
                   "Bad primitive procedure name: ~s" 
                   prim-proc)])))

(define prim-proc?
  (lambda (proc)
    (if (member proc *prim-proc-names*)
        #t
        #f)))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))

;(trace eval-exp)
