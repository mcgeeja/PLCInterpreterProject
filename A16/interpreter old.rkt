#lang racket

(require "../chez-init.rkt")
(provide eval-one-exp)
(require racket/trace)

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

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [quoted-exp
   (data pair?)]
  [and-exp
   (exps (listof expression?))]
  [or-exp
   (exps (listof expression?))]
  [begin-exp
    (exps (listof expression?))]
  [multi-exp
   (exps (listof expression?))]
  [cond-exp
   (tests (listof expression?))
   (values (listof expression?))]
  [let*-exp
   (vars (listof expression?))
   (exps (listof expression?))
   (bodies (listof expression?))]
  [letrec-exp
   (proc-names (listof symbol?))
   (idss (listof (listof symbol?)))
   (bodiess (listof expression?))
   (letrec-bodies (listof expression?))]
  [lit-exp
   (datum
    (lambda (x)
      (ormap 
       (lambda (pred) (pred x))
       (list number? vector? boolean? symbol? string? null? void?))))]
  [vec-exp
   (vec vector?)]
  [let-exp
   (var  (listof expression?))
   (exp1 (listof expression?))
   (body (listof expression?))]
  [lambda-exp
   (ids (listof expression?))
   (body (listof expression?))]
  [normal-lambda-exp
   (id expression?)
   (body (listof expression?))]
  [if-exp
   (condition (listof expression?))
   (true (listof expression?))
   (false (listof expression?))]
  [app-exp
   (rator expression?)
   (rand (listof expression?))]
  [set!-exp
   (id expression?)
   (exp (listof expression?))]
  )
	

; Environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals vector?)
   (env environment?)])


; Datatype for procedures

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
  [letrec-closure
   (ids (listof symbol?))
   (body expression?)
   (env environment?)])

  
;-------------------+
;                   |
;    sec:PARSER     |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; Helper procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
      [(and (pair? datum)(eqv? 'quote (car datum)))  (quoted-exp datum)]
      [((lambda (x)
          (ormap 
           (lambda (pred) (pred x))
           (list number? vector? boolean? symbol? string? null? void?))) datum) (lit-exp datum)]
      [(vector? datum) (vec-exp datum)]
      [(eqv? (1st datum) 'and) (and-exp (map parse-exp (cdr datum)))]
      [(eqv? (1st datum) 'or) (or-exp (map parse-exp (cdr datum)))]
      [(eqv? (1st datum) 'begin) (begin-exp (map parse-exp (cdr datum)))]
      [(eqv? (1st datum) 'cond) (cond-exp
                                 (map (lambda (test)
                                        (parse-exp (1st test))) (cdr datum))
                                 (map (lambda (value)
                                        (parse-exp (2nd value))) (cdr datum)
                                                                 ))]
      [(eqv? (1st datum) 'let*) (let*-exp
                                 (map (lambda (var)
                                        (parse-exp (1st var))) (2nd datum))
                                 (map (lambda (exp)
                                        (parse-exp (2nd exp))) (2nd datum))
                                 (map parse-exp (cddr datum)))]
      [(eqv? (1st datum) 'letrec) (letrec-exp
                                   (map (lambda (param)
                                          (1st param)) (2nd datum))
                                   (map (lambda (id)
                                          (2nd (2nd id))) (2nd datum))
                                   (map (lambda (lambda-body)
                                          (parse-exp (3rd (2nd lambda-body)))) (2nd datum))
                                   (map parse-exp (cddr datum)))]
                                   
      [(pair? datum)
       (cond
         ; handle lambda
         [(eqv? (1st datum) 'lambda)
          (cond [(< (length datum) 3) (error 'parse-exp "invalid lambda format")]
                [(symbol? (2nd datum)) (normal-lambda-exp (parse-exp (2nd datum)) (map parse-exp (cddr datum)))]
                [(not (andmap (lambda (elem) (symbol? elem)) (2nd datum))) (error 'parse-exp "not every parameter is a symbol")]
                [else (lambda-exp (map parse-exp (2nd datum)) (map parse-exp (cddr datum)))])]
         ; handle let variants 
         [(or (eqv? (1st datum) 'let))
          (cond
            ; [(not (andmap (lambda (lst) (list? lst)) (2nd datum))) (error 'parse-exp "invalid parameters for let variant")]
            ;  [(not (andmap (lambda (lst) (= (length lst) 2)) (2nd datum))) (error 'parse-exp "invalid parameters for let variant")]
            ;  [(not (andmap (lambda (lst) (symbol? (first lst))) (2nd datum))) (error 'parse-exp "local variable for lambda is not a symbol")]
            ;  [(< (length datum) 3) (error 'parse-exp "invalid let format")]
            [(symbol? (2nd datum))

             (parse-exp (list 'letrec (list (list (2nd datum)
                                                      (list 'lambda (map (lambda (e1)        
                                                                               (1st e1))
                                                                             (3rd datum))
                                                             (4th datum) )))
                        (append (list (2nd datum))(map (lambda (e2)
                                                         (2nd e2))
                                                       (3rd datum)))))
                 
             ; (letrec-exp  (list (2nd datum))
             ;  (map (lambda (e1)
             ;        (parse-exp
             ;         (1st e1)))
             ;      (3rd datum))
             ; (list (parse-exp (4th datum)))
             ;  (append (list (parse-exp (2nd datum)))(map (lambda (e2)
             ;        (parse-exp (2nd e2)))
             ;   (3rd datum))) ;might need to be a app exp      
             ;  )
             ] 
            [else 
             (let-exp
              (map (lambda (e1)
                     (parse-exp
                      (1st e1)))
                   (2nd datum))
              (map (lambda (e2)
                     (parse-exp (2nd e2)))
                   (2nd datum))
              (map parse-exp (cddr datum)))])]
         ; handle if
         [(eqv? (1st datum) 'if)
          (cond [(< (length datum) 3) (error 'parse-exp "invalid if format")]
                [(= (length datum) 3) (if-exp (map parse-exp (list (2nd datum)))
                                              (map parse-exp (list (3rd datum)))
                                              (map parse-exp (list (void))))]
                [else (if-exp (map parse-exp (list (2nd datum)))
                              (map parse-exp (list (3rd datum)))
                              (map parse-exp (list (4th datum))))])]
         ; handle set!
         [(eqv? (1st datum) 'set!)
          (cond [(not (= (length datum) 3)) (error 'parse-exp "incorrect set! format")]
                [else (set!-exp (2nd datum) (list (map parse-exp (3rd datum))))])]
               
         ;handle app-exp
         [else
          (if (not (list? datum))
              (error 'parse-exp "app not a list")
              (app-exp (parse-exp (1st datum))
                       (map parse-exp (cdr datum)))) ;Map through cdr
          ])] ;Anything with list, map through it
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
    (extended-env-record syms (list->vector vals) env)))

(define iota
  (lambda (val)
    (let helper ([n 0] [lst '()])
      (cond [(eq? n val) lst]
            [else (helper (add1 n) (append lst (list n)))]
            ))))

(define extend-env-recursively
  (lambda (proc-names idss bodiess old-env)
    (let ([len (length proc-names)])
      (let ([vec (make-vector len)])
        (let ([env (extended-env-record
                    proc-names vec old-env)])
         ; (display "IOTA ") (display (iota len)) (newline)
         ; (display "IDS ") (display (length (list idss))) (display idss) (newline)
         ; (display "Bodiess ") (display (length bodiess)) (display bodiess) (newline)
          (for-each
           (lambda (pos ids bodies)
             (vector-set! vec
                          pos
                          (letrec-closure ids bodies env)))
           (iota len)
            idss
            bodiess)
          env)))))

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
                        (apply-env-global sym)]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (vector-ref vals pos)
                                 (apply-env env sym)))]
      
      ;[recursively-extended-env-record
      ;  (proc-names idss bodiess old-env)
      ;              (let ([pos (list-find-position sym proc-names)])
      ;               (if (number? pos)
      ;                   (closure (list-ref idss pos)
      ;                            (list-ref bodiess pos)
      ;                                      env)
      ;                   (apply-env old-env sym)))])))
      )))

(define apply-env-global
  (lambda (sym) 
    (cases environment global-env 
      [empty-env-record ()      
                        (error 'env "variable ~s not found." sym)]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (vector-ref vals pos)
                                 (error 'global-env "Symbol ~s not found" sym)))])))


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
      [quoted-exp (data) exp]
      [vec-exp (vec) exp]
      [multi-exp (exps) exp]
      [let-exp (var exp1 body)
               (list 'let-exp (map syntax-expand var)
                     (map syntax-expand exp1)
                     (map syntax-expand body))]
      [lambda-exp (ids body) exp]
      [normal-lambda-exp (id body) exp]
      [if-exp (condition true false)
              (list 'if-exp (map syntax-expand condition)
                    (map syntax-expand true)
                    (map syntax-expand false))]
      [app-exp (rator rand) exp]
      [set!-exp (id exp) exp]
      [and-exp (exps)
               (cond [(null? exps) (lit-exp #t)]
                     [(null? (cdr exps)) (syntax-expand (car exps))]
                     [else (if-exp (list (syntax-expand (car exps)))
                                   (list (syntax-expand (and-exp (cdr exps))))
                                   (list (lit-exp #f)))])]
      [or-exp (exps)
              (cond [(null? exps) (lit-exp #f)]
                    [(null? (cdr exps)) (syntax-expand (car exps))]
                    [else (if-exp (list (syntax-expand (car exps)))
                                  (list (syntax-expand (car exps)))
                                  (list (syntax-expand (or-exp (cdr exps)))))])]
      [begin-exp (exps)
                 (cond [(null? (cdr exps)) (syntax-expand (car exps))]
                       [else (multi-exp (list (syntax-expand (car exps)) (syntax-expand (begin-exp (cdr exps)))))]
                       )]
      [cond-exp (tests values)
                (cond [(null? (cdr tests)) (if (eqv? (2nd (1st tests)) 'else)
                                               (syntax-expand (1st values))
                                               (if-exp (list (syntax-expand (1st tests)))
                                                       (list (syntax-expand (1st values)))
                                                       (list (lit-exp (void)))))]
                      [else (if-exp (list (syntax-expand (1st tests)))
                                    (list (syntax-expand (1st values)))
                                    (list (syntax-expand (cond-exp (cdr tests)(cdr values)))))]
                      )]
      [let*-exp (vars exps bodies)
                (cond [(null? (cdr vars)) (let-exp vars exps (map syntax-expand bodies))]
                      [else (let-exp (list (car vars)) (list (car exps)) (list (syntax-expand (let*-exp (cdr vars) (cdr exps) bodies))))]
                      )]
      [letrec-exp (proc-names idss bodiess letrec-bodies)
                  (list 'letrec-exp proc-names
                     idss
                     (map syntax-expand bodiess)
                     letrec-bodies)
                  ]
    

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

(define eval-exp
  (lambda (env exp)
    (cases expression exp
      [lit-exp (datum) datum]
      [quoted-exp (data) (cadr data)]
      [var-exp (id)
               (apply-env env id)]
      [app-exp (rator rands)
               (let ([proc-value (eval-exp env rator)]
                     [args (eval-expressions env rands)])
                 (apply-proc proc-value args))]
      [if-exp (condition true false)
              (if (eval-exp env (1st condition))
                  (eval-exp env (1st true))
                  (eval-exp env (1st false)))]
      [let-exp (vars var-exps bodies)
               (eval-bodies (extend-env (map (lambda (e2)
                                               (2nd e2))
                                             vars)
                                        (eval-expressions env var-exps)
                                        env) bodies)]
      [lambda-exp (ids bodies)
                  (closure (map (lambda (e2)(2nd e2)) ids) bodies env)]
      [normal-lambda-exp (id bodies)
                         (single-closure (2nd id) bodies env)]
      [multi-exp (exps)
                 (car (reverse (map (lambda (x)
                                      (eval-exp env x)) exps)))]
      [letrec-exp (proc-names idss bodiess letrec-bodies)
                  (eval-bodies (extend-env-recursively
                                proc-names idss bodiess env) letrec-bodies)]
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-bodies
  (lambda (env bodies)
    (if (null? (cdr bodies))
        (eval-exp env (car bodies))
        (begin
          (eval-exp env (car bodies))
          (eval-bodies env (cdr bodies))))))

(define eval-expressions
  (lambda (env rands)
    (map ((curry eval-exp) env) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.


;Implement closure-proc here, use it to implement the new environment from the closure. Call eval-exp
(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [closure (ids bodies env)
               (eval-bodies (extend-env ids args env) bodies)]
      [single-closure (id bodies env)
                      (eval-bodies (extend-env (list id) (list args) env) bodies)]
      [letrec-closure (ids bodies env)
                      (eval-exp (extend-env ids args env) bodies)]
      ; You will add other cases
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 zero? not cons car cdr list
                              null? assq eq? equal? atom? length list->vector list? pair? procedure?
                              vector->list vector make-vector vector-ref vector? number?
                              symbol? vector-set! display quote = < > <= >=
                              caar cadr cdar cddr caaar caadr cadar caddr cdaar cddar cdadr cdddr
                              append list-tail quotient member? eqv? map apply))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
   *prim-proc-names*   ;  a value (not an expression) with an identifier.
   (map prim-proc      
        *prim-proc-names*)
   (empty-env)))

(define global-env init-env)

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

;Switch to apply for most of these to allow for multiple arguments
(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(zero?) (zero? (1st args))]
      [(not) (not (1st args))]
      [(cons) (cons (1st args) (2nd args))]
      [(car) (car (1st args))]
      [(cdr) (cdr (1st args))]
      [(list) (apply list args)]
      [(null?) (null? (1st args))]
      [(assq) (assq (1st args) (2nd args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      ;[(atom?) (atom? (1st args))]
      [(length) (length (1st args))]
      [(list->vector) (list->vector (1st args))]
      [(list?) (list? (1st args))]
      [(pair?) (pair? (1st args))]
      [(procedure?) (proc-val? (1st args))]
      [(vector->list) (vector->list (1st args))]
      [(vector) (apply vector args)]
      [(make-vector) (make-vector (1st args) (2nd args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector?) (vector? (1st args))]
      [(number?) (number? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(display) (display (1st args) (2nd args))]
      [(newline) (newline)]
      [(quote) (quote args)]
      [(caar) (caar (1st args))]
      [(cadr) (cadr (1st args))]
      [(cdar) (cdar (1st args))]
      [(cddr) (cddr (1st args))]
      [(caaar) (caaar (1st args))]
      [(caadr) (caadr (1st args))]
      [(cadar) (cadar (1st args))]
      [(caddr) (caddr (1st args))]
      [(cdaar) (cdaar (1st args))]
      [(cdadr) (cdadr (1st args))]
      [(cddar) (cddar (1st args))]
      [(cdddr) (cdddr (1st args))]
      [(map) (map (lambda (arguments) (apply-proc (1st args) (list arguments))) (1st (cdr args)))]
      [(apply) (apply-proc (1st args) (2nd args))]
      [(member?) (if (list? (member (1st args) (2nd args))) 
                     #t
                     #f)]
      [(append) (append (1st args) (2nd args))]
      [(eqv?) (eqv? (1st args) (2nd args))]
      [(quotient) (quotient (1st args) (2nd args))]
      [(list-tail) (list-tail (1st args) (2nd args))]
      ; [(and (equal? (get-first-char prim-proc) 'c) (equal? (get-last-char prim-proc) 'r)) ((make-c...r (remove-first-last prim-proc)) (1st args))]
      [(=) (= (1st args) (2nd args))]
      [(<) (< (1st args) (2nd args))]
      [(>) (> (1st args) (2nd args))]
      [(<=) (<= (1st args) (2nd args))]
      [(>=) (>= (1st args) (2nd args))]
      [else (error 'apply-prim-proc 
                   "Bad primitive procedure name: ~s" 
                   prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (syntax-expand (parse-exp (read))))])
      ;; TODO: are there answers that should display differently?
      (pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))



(provide eval-one-exp y2 advanced-letrec)

;; This is the starting code for the Y Combinator final
;; 1 point question.  Dump the y2 and advanced-letrec
;; into your interpreter to get the tests working.
;;
;; Only attempt the question if you are feeling very daring.

(define my-*p
  (lambda (self)
    (lambda (num times)
      (if (zero? times)
          0
          (+ num (self num (sub1 times)))))))

; The Y Combinator: A function that takes a function
; and returns a recursive version of that function

(define yp
  (lambda (self)
    (lambda (f)
      (f (lambda params
         (apply ((self self) f) params)))
    )))

(define y
  (yp yp))

(define my-*
  (y my-*p))



(define-syntax (basic-letrec stx)
   (syntax-case stx ()
     [(basic-letrec prod-name prod-body letrec-body)
      #'(let ((prod-name (y (lambda (prod-name) prod-body))))
          letrec-body)]))

(basic-letrec my-*2 (lambda (num times)
                      (if (zero? times)
                          0
                          (+ num (my-*2 num (sub1 times)))))
              (my-*2 3 4))

(define my-odd?
  (lambda (my-odd? my-even?)
    (lambda (num)
      (if (zero? num)
          #f
          (my-even? (sub1 num))))))
                      
(define my-even?
  (lambda (my-odd? my-even?)
    (lambda (num)
      (if (zero? num)
          #t
          (my-odd? (sub1 num))))))

;; STEP 1 first hand code y2

(define y2
  (lambda (which f1 f2)
    (nyi)))
  
;(define good-odd?
;  (y2 my-odd? my-odd? my-even?))

;(define good-even?
;  (y2 my-even? my-odd? my-even?))


(define-syntax (advanced-letrec stx)
  (syntax-case stx ()
    [(advanced-letrec ((fun-name fun-body)...) letrec-body)
     #'(error "nyi")]))

; just an example for you to see advanced letrec in action

;(advanced-letrec
; ((odd-last? (lambda (num)
;               (if (zero? num)
;                   #f
;                   (even-last? (sub1 num)))))
;  (even-last? (lambda (num)
;                (if (zero? num)
;                    #t
;                    (odd-last? (sub1 num))))))
; (even-last? 6))

(define-syntax nyi
  (syntax-rules ()
    ([_]
     [error "nyi"])))