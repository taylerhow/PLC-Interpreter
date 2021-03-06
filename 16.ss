; Tayler How, Jesse Shellabarger, & Chase Bishop, Assignment 16 11/1/15

;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

;(load "chez-init.ss")

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
		(arg (list-of symbol?))
		(bodies (list-of expression?))
	]
	[improper-lambda-exp
		(defined-args (list-of symbol?))
		(undefined-args symbol?)
		(bodies (list-of expression?))
	]
	[app-exp
		(rator expression?)
		(rand (list-of expression?))
	]
	[if-exp
		(condition expression?)
		(truecase expression?)
		(falsecase expression?)
	]
	[set!-exp
		(var expression?)
		(val expression?)
	]
	[while-exp
		(condition expression?)
		(bodies (list-of expression?))
	]
	[letrec-exp
		(proc-names (list-of symbol?))
		(ids (list-of (list-of symbol?)))
		(bodies (list-of (list-of expression?)))
		(letrec-bodies (list-of expression?))
	]
	[improper-letrec-exp
		(proc-names (list-of symbol?))
		(ids (list-of pair?))
		(bodies (list-of (list-of expression?)))
		(letrec-bodies (list-of expression?))
	]
	
	
	; Syntax
	[named-let-syn
		(name symbol?)
		(vars (list-of symbol?))
		(vals (list-of expression?))
		(bodies (list-of expression?))
	]
	[let-syn
		(vars (list-of symbol?))
		(vals (list-of expression?))
		(bodies (list-of expression?))
	]
	[begin-syn
		(bodies (list-of expression?))
	]
	[cond-syn
		(conditions (list-of expression?))
		(bodies (list-of (list-of expression?)))
	]
	[else-syn
		(bool boolean?)
	]
	[and-syn
		(bodies (list-of expression?))
	]
	[or-syn
		(bodies (list-of expression?))
	]
	[let*-syn
		(vars (list-of symbol?))
		(vals (list-of expression?))
		(bodies (list-of expression?))
	]
	[case-syn
		(var expression?)
		(conditions (list-of expression?))
		(bodies (list-of expression?))
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
		(env environment?))
	(recursive-env-record
		(proc-names (list-of symbol?))
		(ids (list-of (list-of symbol?)))
		(bodies (list-of (list-of expression?)))
		(old-env environment?)
	)
	(improper-recursive-env-record
		(proc-names (list-of symbol?))
		(ids (list-of pair?))
		(bodies (list-of (list-of expression?)))
		(old-env environment?)
	)
)

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
	[prim-proc (name symbol?)]
	[closure
		(vars (list-of symbol?))
		(bodies (list-of expression?))
		(env environment?)
	]
	[improper-closure
		(vars (list-of symbol?))			; This looks the same as a closure but will allow us to check for closures that are improper in apply-closure
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

; Tayler How, Chase Bishop & Jesse Shellabarger, Parser stuffs, created 10/11/15
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

; TODO: chase is irritated w/ (list jankness)
(define parse-exp
	(lambda (datum)
		(cond
			[(and (not (eqv? 'else datum)) (symbol? datum)) (list 'var-exp datum)]
			[(or (number? datum) (boolean? datum) (vector? datum) (string? datum)) (list 'lit-exp datum)]
			[(list? datum)
				(cond
					[(eqv? (1st datum) 'lambda)
						(cond
							[(list? (2nd datum))
								(begin
									(validate-lambda-exp datum)
									(list
										'lambda-exp
										(2nd datum)
										(inorder-map parse-exp (cddr datum))
									)
								)
							]
							; TODO: add error checking for this case
							[(pair? (2nd datum))
								(begin
									(let ([args (parse-pair (2nd datum))])
										(improper-lambda-exp (car args) (cadr args) (inorder-map parse-exp (cddr datum)))
									)
								)
							]
							[(symbol? (2nd datum))
								(improper-lambda-exp '() (2nd datum) (inorder-map parse-exp (cddr datum)))
							]
							[else (eopl:error 'parse-exp "i cry every tim bad lambda" datum)]
						)
					]
					[(eqv? (1st datum) 'if)
						(begin
							(validate-if-exp datum)
							(list
								'if-exp
								(parse-exp (2nd datum))
								(parse-exp (3rd datum))
								(if (null? (cdddr datum))
									(parse-exp '(void))
									(parse-exp (4th datum))
								)
							)
						)
					]
					[(eqv? (1st datum) 'let)
						(if (symbol? (2nd datum))
							;named let
							(named-let-syn 
								(2nd datum)
								(inorder-map car (3rd datum))
								(inorder-map parse-exp (inorder-map cadr (3rd datum)))
								(inorder-map parse-exp (cdddr datum))
							)
							;regular let
							(begin
								(validate-let-type-exp datum)
								(list
									'let-syn
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
							(let*-syn
								(inorder-map car (2nd datum))
								(inorder-map parse-exp (inorder-map cadr (2nd datum)))
								(inorder-map parse-exp (cddr datum))
							)
						)
					]
					[(eqv? (1st datum) 'letrec)
						(begin
							(validate-let-type-exp datum)
							(if (andmap list? (inorder-map cadr (inorder-map cadr (2nd datum))))
								(letrec-exp 
									(inorder-map car (2nd datum))
									(inorder-map cadr (inorder-map cadr (2nd datum))) 
									(inorder-map (lambda (x) (inorder-map parse-exp x)) (inorder-map cddr (inorder-map cadr (2nd datum)))) 
									(inorder-map parse-exp (cddr datum)))
								(improper-letrec-exp
									(inorder-map car (2nd datum))
									(inorder-map cadr (inorder-map cadr (2nd datum)))
									(inorder-map (lambda (x) (inorder-map parse-exp x)) (inorder-map cddr (inorder-map cadr (2nd datum)))) 
									(inorder-map parse-exp (cddr datum))
								)	
							)
							
						)
					]
;;					[(eqv? (1st datum) 'set!)
;;						(begin
;;							(validate-set!-exp datum)
;;							(list
;;								'set!-exp
;;								(parse-exp (2nd datum))
;;								(parse-exp (3rd datum))
;;							)
;;						)
;;					]
					[(eqv? (1st datum) 'quote)
						(list
							'lit-exp
							(2nd datum)
						)
					]
					
					; SYNTAX
					[(eqv? (1st datum) 'begin)
						(begin-syn (inorder-map parse-exp (cdr datum)))
					]
					
					[(eqv? (1st datum) 'cond)
						(cond-syn (inorder-map parse-exp (inorder-map car (cdr datum))) 
									(inorder-map (lambda (x) (inorder-map parse-exp x)) (inorder-map cdr (cdr datum)))) 
					]
					
					[(eqv? (1st datum) 'and)
						(and-syn (inorder-map parse-exp (cdr datum)))
					]
					
					[(eqv? (1st datum) 'while)
						(while-exp (parse-exp (cadr datum)) (inorder-map parse-exp (cddr datum)))
					]
					
					[(eqv? (1st datum) 'or)
						(or-syn (inorder-map parse-exp (cdr datum)))
					]
					
					[(eqv? (1st datum) 'case)
						(case-syn 
							(parse-exp (cadr datum)) 
							(inorder-map (lambda (x) (if (eqv? 'else x) (else-syn #t) (app-exp (var-exp 'list) (map parse-exp x)))) (inorder-map car (cddr datum)))
							(inorder-map (lambda (x) (parse-exp (cadr x))) (cddr datum))
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
			; This needs to be checked outside of the list? condition branch
			[(eqv? datum 'else)
						(else-syn #t)
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
		(if (or
				(and (not (null? (cdr datum))) (not (null? (cddr datum))) (null? (cdddr datum)))
				(not (or (null? (cdr datum)) (null? (cddr datum)) (null? (cdddr datum)) (not (null? (cddddr datum)))))
			)
			#t
			(eopl:error 'parse-exp "if-expression ~s does not have (only) test, then, and (possibly) else" datum)
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

(define parse-pair
	(lambda (p)
		(if (not (pair? (cdr p)))
			(cons (list (car p)) (list (cdr p)))
			(let ([rec (parse-pair (cdr p))])
				(cons (cons (car p) (car rec)) (cdr rec))
			)
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
						(apply-env env sym succeed fail)))
			)
			(recursive-env-record (proc-names ids bodies old-env)
				(let ([pos (list-find-position sym proc-names)])
					(if (number? pos)
						(closure (list-ref ids pos) (list-ref bodies pos) env)
						(apply-env old-env sym succeed fail)
					)	
				)
			)
			(improper-recursive-env-record (proc-names ids bodies old-env)
				(let ([pos (list-find-position sym proc-names)])
					(if (number? pos)
						(let ([current-id (list-ref ids pos)])
							(if (list? current-id)
								(closure current-id (list-ref bodies pos) env)
								(improper-closure (flatten-improper-list current-id) (list-ref bodies pos) env)
							)
						)
						(apply-env old-env sym succeed fail)
					)	
				)
			)
		)
	)	
)








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+

(define syntax-expand
	(lambda (e)
		(cases expression e
		
			;Syntax
			[let-syn (vars vals bodies)
				(app-exp (lambda-exp vars (inorder-map syntax-expand bodies)) (inorder-map syntax-expand vals))
			]
			[begin-syn (bodies)
				(app-exp (lambda-exp '() (inorder-map syntax-expand bodies)) '())
			]
			[cond-syn (conditions bodies)
				(if-exp (syntax-expand (car conditions)) 
						(syntax-expand (begin-syn (inorder-map syntax-expand (car bodies))))
						(if (null? (cdr conditions))
							(app-exp (var-exp 'void) '())
							(syntax-expand (cond-syn (cdr conditions) (cdr bodies))))
						)
			]
			[else-syn (bool)
				(lit-exp #t)
			]
			[and-syn (bodies)
				(if (null? bodies)
					(lit-exp #t)
					(if-exp (syntax-expand (car bodies))
							(if (null? (cdr bodies))
								(syntax-expand (car bodies))
								(syntax-expand (and-syn (cdr bodies)))
							)
						(lit-exp #f)
					)
				)
					
			]
			[or-syn (bodies)
				(if (null? bodies)
					(lit-exp #f)
					(if-exp (syntax-expand (car bodies))
						(syntax-expand (car bodies))
						(if (null? (cdr bodies))
							(lit-exp #f)
							(syntax-expand (or-syn (cdr bodies)))
						)
				)
				)
				
			]
			[let*-syn (vars vals bodies)
				(syntax-expand (let*-syn->let-syn vars vals bodies))
			]
			
			[named-let-syn (name vars vals bodies)
				(letrec-exp (list name) (list vars)	(list (inorder-map syntax-expand bodies)) (list (app-exp (var-exp name) (inorder-map syntax-expand vals))))
			]
				
			
			[case-syn (var conditions bodies)
				(if (null? conditions) 
					(app-exp (var-exp 'void) '())
					(if (eqv? 'else-syn (caar conditions))
						(syntax-expand (car bodies))
						(if-exp (app-exp (var-exp 'memq) (list var (car conditions)))
							(syntax-expand (car bodies))
							(syntax-expand (case-syn var (cdr conditions) (cdr bodies)))
						)
					)
				)
			]
			
			; Expressions
			[lambda-exp (vars bodies)
				(lambda-exp vars (inorder-map syntax-expand bodies))
			]
			[improper-lambda-exp (defined-args undefined-args bodies)
				(improper-lambda-exp defined-args undefined-args (inorder-map syntax-expand bodies))
			]
			[if-exp (condition truecase falsecase)
				(if-exp (syntax-expand condition) (syntax-expand truecase) (syntax-expand falsecase))
			]
			[while-exp (condition bodies)
				(while-exp (syntax-expand condition) (inorder-map syntax-expand bodies))
			]
			[letrec-exp (proc-names ids bodies letrec-bodies)
				(letrec-exp proc-names ids (inorder-map (lambda (x) (inorder-map syntax-expand x)) bodies) (inorder-map syntax-expand letrec-bodies))
			]
			[improper-letrec-exp (proc-names ids bodies letrec-bodies)
				(improper-letrec-exp proc-names ids (inorder-map (lambda (x) (inorder-map syntax-expand x)) bodies) (inorder-map syntax-expand letrec-bodies))
			]
			[app-exp (rator rand)
				(app-exp (syntax-expand rator) (inorder-map syntax-expand rand))
			]
			[lit-exp (lit)
				e
			]
			[var-exp (var)
				e
			]
			[else 
				(eopl:error 'syntax-expand "Expression is not an expression variant ~s" e)
			]
		)
	)
)

(define let*-syn->let-syn
	(lambda (vars vals bodies)
		(let-syn
			(list (car vars))
			(list (car vals))
			(if (null? (cdr vars))
				bodies
				(list (let*-syn->let-syn (cdr vars) (cdr vals) bodies))
			)
		)
	)
)

(define case-syn-helper
	(lambda (var conds)
		(let loop ([conditions conds])
			(cond
				[(null? conditions) '()]
				[else (cons (app-exp (var-exp 'memq) (list var (car conditions))) (loop (cdr conditions)))]			
			)
		)
	)
)



;-------------------+
;                   |
;   INTERPRETER    	|
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
			[lambda-exp (args bodies)
				(closure args bodies env)
			]
			[improper-lambda-exp (defined-args undefined-args bodies)				; Simply makes a closure that has the undefined-args as the last variable
				(improper-closure (append defined-args (list undefined-args)) bodies env)
			]
			[while-exp (condition bodies)
				(let loop ([return '()])
						(if (eval-exp condition env)
							(loop (return-inorder-map (lambda (x) (eval-exp x env)) bodies))
							return
						)
				)
			]
			[letrec-exp (proc-names ids bodies letrec-bodies)
				(let ([new-env (recursive-env-record proc-names ids bodies env)])
					(return-inorder-map (lambda (x) (eval-exp x new-env)) letrec-bodies)
				)
			]
			[improper-letrec-exp (proc-names ids bodies letrec-bodies)
				(let ([new-env (improper-recursive-env-record proc-names ids bodies env)])
					(return-inorder-map (lambda (x) (eval-exp x new-env)) letrec-bodies)
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
		(inorder-map (lambda (x) (eval-exp x env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
	(lambda (proc-value args)
		(cases proc-val proc-value
		[prim-proc (op) (apply-prim-proc op args)]
		[closure (vars body env) (apply-closure vars body env args)]
		[improper-closure (vars body env) 
			(apply-closure vars body env (improper-closure-vals-init vars args))
		]
		[else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))
					
(define apply-closure
	(lambda (vars bodies env args)
		(let ([new-env (extend-env vars args env)])
			(return-inorder-map (lambda (x) (eval-exp x new-env)) bodies)
		)
	)
)

(define *prim-proc-names* '(+ - * / add1 sub1 cons = > < <= >= zero? not car cdr list null? assq eq? equal? atom? 
							length list->vector list? pair? procedure? vector->list vector make-vector vector-ref 
							vector? number? symbol? set-car! set-cdr! vector-set! display newline caar cadr 
							cdar cddr caaar caadr cadar cdaar caddr cdadr cddar cdddr quote void apply map memq quotient
							append eqv? list-tail))

(define init-env         ; for now, our initial global environment only contains 
	(extend-env            ; procedure names.  Recall that an environment associates
		*prim-proc-names*   ;  a value (not an expression) with an identifier.
		(map prim-proc      
			*prim-proc-names*)
			(empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

; TODO: Change all of these to apply because :(
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
			[(zero?) (apply zero? args)]
			[(not) (apply not args)]
			[(car) (apply car args)]
			[(cdr) (apply cdr args)]
			[(list) (apply list args)]
			[(null?) (apply null? args)]
			[(assq) (apply assq args)]
			[(eq?) (apply eq? args)]
			[(equal?) (apply equal? args)]
			[(atom?) (apply atom? args)]
			[(length) (apply length args)]
			[(list->vector) (list->vector (car args))]
			[(list?) (list? (car args))]
			[(pair?) (pair? (car args))]
			[(procedure?) (proc-val? (car args))]
			[(vector->list) (vector->list (car args))]
			[(vector) (apply vector args)]
			[(vector-ref) (apply vector-ref args)]
			[(make-vector) (apply make-vector args)]
			[(caar) (apply caar args)]
			[(cadr) (apply cadr args)]
			[(cdar) (apply cdar args)]
			[(cddr) (apply cddr args)]
			[(caaar) (apply caaar args)]
			[(caadr) (apply caadr args)]
			[(cadar) (apply cadar args)]
			[(cdaar) (apply cdaar args)]
			[(caddr) (apply caddr args)]
			[(cddar) (apply cdaar args)]
			[(cdddr) (apply cdddr args)]
			[(cdadr) (apply cdadr args)]
			[(newline) (newline)]
			[(display) (begin (display (car args)) (newline))]
			[(vector-set!) (apply vector-set! args)]
			[(set-cdr!) (apply set-cdr! args)]
			[(set-car!) (apply set-car! args)]
			[(symbol?) (apply symbol? args)]
			[(number?) (apply number? args)]
			[(vector?) (apply vector? args)]
			[(void) (void)]
			[(apply) (apply-proc (car args) (cadr args))]
			[(quote) (quote (car args))]
			[(map)
				(let loop ([proc (car args)] [rest (cadr args)])
					(if (null? rest)
						'()
						(cons (apply-proc proc (list (car rest))) (loop proc (cdr rest)))
					)
				)
			]
			[(memq) (apply memq args)]
			[(quotient) (apply quotient args)]
			[(append) (apply append args)]
			[(eqv?) (apply eqv? args)]
			[(list-tail) (apply list-tail args)]
			
;			[(set!) (apply set! args)]
			[else (error 'apply-prim-proc 
				"Bad primitive procedure name: ~s" 
				prim-proc)]
		)
	)
)

(define rep      ; "read-eval-print" loop.
	(lambda ()
		(display "--> ")
		;; notice that we don't save changes to the environment...[answer (top-level-eval (syntax-expand (parse-exp (read))))]
		(let* ([parsed-exp (parse-exp (read))] [expanded-exp (syntax-expand parsed-exp)] [answer (top-level-eval expanded-exp)])
			(cond
				[(and (list? answer) (or (eqv? (car answer) 'closure) (eqv? (car answer) 'improper-closure))) (begin (eopl:pretty-print "#<procedure>") (newline) (rep))]
				[(eqv? answer (void)) (rep)]
				[else (begin (eopl:pretty-print answer) (newline) (rep))]
			)
		)
	)
)  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))

; our own map
(define inorder-map
	(lambda (proc ls)
		(if (null? ls)
			'()
			(cons (proc (car ls)) (inorder-map proc (cdr ls)))
		)
	)
)

; TODO: replace all that reverse car crap with this
(define return-inorder-map
	(lambda (proc ls)
		(cond
			[(null? (cdr ls)) (proc (car ls))]
			[else (begin (proc (car ls)) (return-inorder-map proc (cdr ls)))]
		)
	)
)

(define improper-closure-vals-init
	(lambda (vars args)
		(let ([num-defined-vars (- (length vars) 1)])
			(let loop ([output '()] [rest args])
				(cond
					[(equal? (length output) num-defined-vars) (append output (list rest))]
					[else (loop (append output (list (car rest))) (cdr rest))]
				)
			)
		)
	)
)

(define flatten-improper-list
	(lambda (lst)
		(cond 
			[(null? lst) '()]
			[(list? lst) lst]
			[(pair? lst)
				(cons (car lst) (flatten-improper-list (cdr lst)))
			]
			[else (list lst)]
		)
	)
)
