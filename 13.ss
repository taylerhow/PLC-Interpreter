; Tayler How & Jesse Shellabarger, Assignment 13 10/19/15

;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss")

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression

; expression datatype
(define-datatype expression expression?
	[var-exp
		(var symbol?)
	]
	[lit-exp
		(lit literal?)
	]
	[lambda-exp
		(arg symbol?)
		(body expression?)
	]
	[app-exp
		(rator expression?)
		(rand expression?)
	]
	[if-exp
		(condition expression?)
		(truecase expression?)
		(falsecase expression?)
	]
	[let-exp
;		(app expression?) old way
		(vars (list-of symbol?))
		(vals (list-of expression?))
		(bodies (list-of expression?))
	]
	[let*-exp
		(app expression?)
	]
	[letrec-exp
		(app expression?)
	]
	[set!-exp
		(var expression?)
		(val expression?)
	]
)

(define literal?
	(lambda (obj)
		(or (number? obj) (boolean? obj) (vector? obj) (string? obj) (symbol? obj) (and (list? obj) (eqv? 'quote (car obj))) (null? obj))
	)
)
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
	(empty-env-record)
	(extended-env-record
		(syms (list-of symbol?))
		(vals (list-of scheme-value?))
		(env environment?)))

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
	[prim-proc (name symbol?)]
	[closure
		(vars (list-of symbol?))
		(bodies (list-of expression?))
		(env environment?)
	]
)
	 
	

;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Tayler How & Jesse Shellabarger, Parser stuffs, created 10/11/15
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

(define parse-exp
	(lambda (datum)
		(cond
			[(symbol? datum) (list 'var-exp datum)]
			[(or (number? datum) (boolean? datum) (vector? datum) (string? datum)) (list 'lit-exp datum)]
			[(list? datum)
				(cond
					[(eqv? (1st datum) 'lambda)
						; error checking
						(begin
							(validate-lambda-exp datum)
							(list
								'lambda-exp
								(2nd datum)
								(map parse-exp (cddr datum))
							)
						)
					]
					[(eqv? (1st datum) 'if)
						(begin
							(validate-if-exp datum)
							(list
								'if-exp
								(parse-exp (2nd datum))
								(parse-exp (3rd datum))
								(parse-exp (4th datum))
							)
						)
					]
					[(eqv? (1st datum) 'let)
						(if (symbol? (2nd datum))
							;named let
							(list
								'let-exp
								(2nd datum)
;								(parse-exp (let->application (cons (1st datum) (cddr datum))))
								(inorder-map car (3nd datum))
								(inorder-map parse-exp (inorder-map cadr (3nd datum)))
								(inorder-map parse-exp (cdddr datum))
							)
							;regular let
							(begin
								(validate-let-type-exp datum)
								(list
									'let-exp
;									(parse-exp (let->application datum)) too awesome :(
									(inorder-map car (2nd datum))
									(inorder-map parse-exp (inorder-map cadr (2nd datum)))
									(inorder-map parse-exp (cddr datum))
								)
							)
						)
					]
					[(eqv? (1st datum) 'let*)
						(begin
							(validate-let-type-exp datum)
							(list
								'let*-exp
								(parse-exp (let->application (let*->let datum)))
							)
						)
					]
					[(eqv? (1st datum) 'letrec)
						(begin
							(validate-let-type-exp datum)
							(list
								'letrec-exp
								(parse-exp (let->application datum))
							)
						)
					]
					[(eqv? (1st datum) 'set!)
						(begin
							(validate-set!-exp datum)
							(list
								'set!-exp
								(parse-exp (2nd datum))
								(parse-exp (3rd datum))
							)
						)
					]
					[(eqv? (1st datum) 'quote)
						(list
							'lit-exp
							(2nd datum)
						)
					]
					[else
						(list
							'app-exp
							(parse-exp (1st datum))
							(map parse-exp (cdr datum))
						)
					]
				)
			]
			[(pair? datum)
				(eopl:error 'parse-exp "expression ~s is not a proper list" datum)
			]
			[else (eopl:error 'parse-exp "Invalid concrete syntax ~s" datum)]
		)
	)
)

; Helpers for invalid input & error catching in parse-exp
(define validate-lambda-exp
	(lambda (datum)
		(cond
			[(or (null? (cdr datum)) (null? (cddr datum)))
				(eopl:error 'parse-exp "lambda-expression: incorrect length ~s" datum)
			]
			[(and (list? (cadr datum)) (not (andmap symbol? (cadr datum))))
				(eopl:error 'parse-exp "lambda's formal arguments ~s must all be symbols" (cadr datum))
			]
			[(and (not (list? (cadr datum))) (not (symbol? (cadr datum))))
				(eopl:error 'parse-exp "lambda's formal arguments ~s must all be symbols" (cadr datum))
			]
			[else #t]
		)
	)
)

(define validate-if-exp
	(lambda (datum)
		(if (or (null? (cdr datum)) (null? (cddr datum)) (null? (cdddr datum)) (not (null? (cddddr datum))))
			(eopl:error 'parse-exp "if-expression ~s does not have (only) test, then, and else" datum)
			#t
		)
	)
)

(define validate-let-type-exp
	(lambda (datum)
		(cond
			[(or (null? (cdr datum)) (null? (cddr datum)))
				(eopl:error 'parse-exp "~s-expression has incorrect length ~s" (car datum) datum)
			]
			[(not (list? (cadr datum)))
				(eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" (car datum) datum)
			]
			[(not 	(andmap 
						(lambda (block) 
							(and (list? block) (not (null? (cdr block))) (null? (cddr block)))
						)
						(cadr datum)
					))	
				(eopl:error 'parse-exp "declaration in ~s-exp must be a proper list of length 2 ~s" (car datum) datum)
			]
			[(not 	(andmap 
						(lambda (2list)
							(symbol? (car 2list))
						)
						(cadr datum)
					))
				(eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" (car datum) datum)
			]
			[else #t]
		)
	)
)

(define validate-set!-exp
	(lambda (datum)
		(if (or (null? (cdr datum)) (null? (cddr datum)) (not (null? (cdddr datum))))
			(eopl:error 'parse-exp "set!-expression ~s does not have (only) variable and expression" datum)
			#t
		)
	)
)

; unparse-exp
(define unparse-exp
	(lambda (e)
		(cases expression e
			[var-exp (var) var]
			[lit-exp (lit) lit]
			[lambda-exp (args body)
				(append (list 'lambda args) (map unparse-exp body))]
			[app-exp (rator rand)
				(cons (unparse-exp rator) (map unparse-exp rand))
			]
			[if-exp (condition truecase falsecase)
				(list
					'if
					(unparse-exp condition)
					(unparse-exp truecase)
					(unparse-exp falsecase)
				)
			]
			[let-exp (app)
				(application->let (unparse-exp app))
			]
			[let*-exp (app)
				; need to handle writing 'let* in the let->let* fxn
				(cons 'let*
					(cdr (let->let* (application->let (unparse-exp app))))
				)
			]
			[letrec-exp (app)
				(application->letrec (unparse-exp app))
			]
			[set!-exp (var val)
				(list
					'set!
					(unparse-exp var)
					(unparse-exp val)
				)
			]
		)
	)
)

; let->application and let*->let from Assignment 6
(define get-lambda-params
	(lambda (block)
		(cond
			[(null? block) block]
			[(null? (cdr block)) (list (caar block))]
			[else (cons (caar block) (get-lambda-params (cdr block)))]
		)
	)
)

(define get-lambda-args
	(lambda (block)
		(cond
			[(null? block) block]
			[(null? (cdr block)) (list (cadar block))]
			[else (cons (cadar block) (get-lambda-args (cdr block)))]
		)
	)
)

(define let->application
	(lambda (block)
		(append (list (append (list 'lambda (get-lambda-params (cadr block))) (cddr block))) (get-lambda-args (cadr block)))
	)
)

(define nested-let-builder
	(lambda (block arg)
		(cond
			[(null? block) block]
			[(null? (cdr block)) (append (list 'let (list (car block))) arg)]
			[else (list 'let (list (car block)) (nested-let-builder (cdr block) arg))]
		)
	)
)

; let*->let
(define let*->let
	(lambda (block)
		(nested-let-builder (cadr block) (cddr block))
	)
)

;  application->let
(define application->let
	(lambda (block)
		(append
			(list
				'let
				(get-let-bindings block)
			)
			(cddar block)
		)
	)
)

(define application->letrec
	(lambda (block)
		(append
			(list
				'letrec
				(get-let-bindings block)
			)
			(cddar block)
		)
	)
)

(define get-let-bindings
	(lambda (block)
		(map list (cadar block) (cdr block))
	)
)

; let->let*
(define let->let*
	(lambda (expression)
		;(caddr block) is the (possibly) nested let statement
		; need to loop to account for multiple nested let statements
		(let loop ([block expression])
			(if (and (list? (caddr block)) (or (eqv? (car block) 'let) (eqv? (car block) 'let*)) (eqv? (car (caddr block)) 'let))
				(loop
					(append
						(list
							'let*
							(append (cadr block) (cadr (caddr block)))
						)
						(cddr (caddr block))
					)
				)
				block
			)
		)
	)
)
;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+





; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

(define empty-env
	(lambda ()
		(empty-env-record)))

(define extend-env
	(lambda (syms vals env)
		(extended-env-record syms vals env)))

(define list-find-position
	(lambda (sym los)
		(list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
	(lambda (pred ls)
		(cond
			((null? ls) #f)
			((pred (car ls)) 0)
			(else (let ((list-index-r (list-index pred (cdr ls))))
				(if (number? list-index-r)
					(+ 1 list-index-r)
					#f))))))

(define apply-env
	(lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
		(cases environment env
			(empty-env-record ()
				(fail))
			(extended-env-record (syms vals env)
				(let ([pos (list-find-position sym syms)])
					(if (number? pos)
						(succeed (list-ref vals pos))
						(apply-env env sym succeed fail)))))))








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



; To be added later









;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define top-level-eval
	(lambda (form)
		; later we may add things that are not expressions.
		(eval-exp form init-env)))

; eval-exp is the main component of the interpreter

(define eval-exp
	(lambda (e env)
		(cases expression e
			[lit-exp (datum) datum]
			[var-exp (id)
				; look up its value.
				(apply-env env id
					(lambda (x) x) ; procedure to call if id is in the environment 
					; procedure to call if id not in env
					(lambda () (apply-env init-env id
						(lambda (x) x) ; procedure to call if id is in the environment 
						; procedure to call if id not in env
						(lambda () (eopl:error 'apply-env "variable not found in environment: ~s" id)))
					)
				)
			  ]
			[if-exp (condition truecase falsecase)
				(if (eval-exp condition env)
					(eval-exp truecase env)
					(eval-exp falsecase env)
				)
			]
			[lambda-exp (args body)
				(closure args body env)
			]
			[let-exp (vars vals bodies)
;				(eval-exp app env) too easy :(
				(let ([new-env (extend-env vars (inorder-map (lambda (x) (eval-exp x env)) vals) env)])
					(car (reverse (inorder-map (lambda (x) (eval-exp x new-env)) bodies)))
				)
			]
			[app-exp (rator rands)
				(let ([proc-value (eval-exp rator env)] [args (eval-rands rands env)])
					(apply-proc proc-value args)
				)
			]
			[else (eopl:error 'eval-exp "Bad abstract syntax: ~a" e)]
		)
	)
)

; evaluate the list of operands, putting results into a list

(define eval-rands
	(lambda (rands env)
		(map (lambda (x) (eval-exp x env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
	(lambda (proc-value args)
		(cases proc-val proc-value
		[prim-proc (op) (apply-prim-proc op args)]
		[closure (vars body env) (apply-closure vars body env args)]
		[else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))
					
(define apply-closure
	(lambda (vars body env args)
		(let ([new-env (extend-env vars args env)])
			(car (reverse (inorder-map (lambda (x) (eval-exp x new-env)) body)))
		)
	)
)

(define *prim-proc-names* '(+ - * / add1 sub1 cons = > < <= >= zero? not car cdr list null? assq eq? equal? atom? 
							length list->vector list? pair? procedure? vector->list vector make-vector vector-ref 
							vector? number? symbol? set-car! set-cdr! vector-set! display newline caar cadr 
							cdar cddr caaar caadr cadar cdaar caddr cdadr cddar cdddr))

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
			[(add1) (apply (lambda (x) (+ x 1)) args)]
			[(sub1) (apply (lambda (x) (- x 1)) args)]
			[(cons) (apply cons args)]
			[(=) (apply = args)]
			[(>) (apply > args)]
			[(<) (apply < args)]
			[(<=) (apply <= args)]
			[(>=) (apply >= args)]
			[(zero?) (andmap zero? args)]
			[(not) (not (car args))]
			[(car) (car (car args))]
			[(cdr) (cdr (car args))]
			[(list) (apply list args)]
			[(null?) (null? (car args))]
			[(assq) (apply assq args)]
			[(eq?) (apply eq? args)]
			[(equal?) (apply equal? args)]
			[(atom?) (atom? (car args))]
			[(length) (length (car args))]
			[(list->vector) (list->vector (car args))]
			[(list?) (list? (car args))]
			[(pair?) (pair? (car args))]
			[(procedure?) (proc-val? (car args))]
			[(vector->list) (vector->list (car args))]
			[(vector) (apply vector args)]
			[(vector-ref) (apply vector-ref args)]
			[(caar) (caar (car args))]
			[(cadr) (cadr (car args))]
			[(cdar) (cdar (car args))]
			[(cddr) (cddr (car args))]
			[(caaar) (caaar (car args))]
			[(caadr) (caadr (car args))]
			[(cadar) (cadar (car args))]
			[(cdaar) (cdaar (car args))]
			[(caddr) (caddr (car args))]
			[(cddar) (cdaar (car args))]
			[(cdddr) (cdddr (car args))]
			[(cdadr) (cdadr (car args))]
			[(newline) (newline)]
			[(display) (display (car args))]
			[(vector-set!) (apply vector-set! args)]
			[(set-cdr!) (apply set-cdr! args)]
			[(set-car!) (apply set-car! args)]
			[(symbol?) (symbol? (car args))]
			[(number?) (number? (car args))]
			[(vector?) (vector? (car args))]
			[else (error 'apply-prim-proc 
				"Bad primitive procedure name: ~s" 
				prim-proc)]
		)
	)
)

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))

; our own map
(define inorder-map
	(lambda (proc ls)
		(if (null? ls)
			'()
			(cons (proc (car ls)) (inorder-map proc (cdr ls)))
		)
	)
)







