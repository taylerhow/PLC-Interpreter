; Tayler How, Jesse Shellabarger, & Chase Bishop, Assignment 16 11/1/15

;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

;(load "chez-init.ss")

;-------------------+
;                   |
;  	ETC. Helpers    |
;                   |
;-------------------+


; Our own version of map that evalutes list items in order

(define inorder-map
	(lambda (proc ls)
		(if (null? ls)
			'()
			(let ([val (proc (car ls))])
				(cons val (inorder-map proc (cdr ls)))
			)
		)
	)
)


(define inorder-map-cps
	(lambda (proc ls k)
		(if (null? ls)
			(apply-k k '())
			(proc
				(car ls) 
				(inorder-map-k proc (cdr ls) k)
			)
		)
	)
)


(define return-inorder-map
	(lambda (proc ls)
		(cond
			[(null? (cdr ls)) (proc (car ls))]
			[else (return-inorder-map proc (cdr ls))]
		)
	)
)

(define return-inorder-map-cps
	(lambda (proc ls k)
		(cond
			[(null? (cdr ls)) (proc (car ls) k)]
			[else
				(proc
					(car ls)
					(return-inorder-map-k proc (cdr ls) k)
				)
			]
		)
	)
)

;; Primitive
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

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+


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
#|	[ref-lambda-exp
		(args (list-of (list-of symbol?)))
		(bodies (list-of expression?))
	] |#
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
	[set-exp
		(id symbol?)
		(new-val expression?)
	]
	[exit-list-exp
		(args (list-of expression?))
	]
	[define-exp
		(id symbol?)
		(new-val expression?)
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
	[continuation-proc (k continuation?)]
	; This looks the same as a closure but will allow us to check for closures that are improper in apply-closure
	[improper-closure
		(vars (list-of symbol?))
		(bodies (list-of expression?))
		(env environment?)
	]
#|	[ref-closure
		(vars (list-of (list-of symbol?)))
		(bodies (list-of expression?))
		(env environment?)
	] |#
)
	 
;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+

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
							[((list-of symbol?) (2nd datum))
								(begin
									(validate-lambda-exp datum)
									(lambda-exp
										(2nd datum)
										(inorder-map parse-exp (cddr datum))
									)
								)
							]
							#| [(list? (2nd datum))
								(begin
									;;validation here
									(ref-lambda-exp
										(make-ref-args (2nd datum))
										(inorder-map parse-exp (cddr datum))
									)
								)
							] |#
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
							(if-exp
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
								(let-syn
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
					
					[(eqv? (1st datum) 'quote)
						(list
							'lit-exp
							(2nd datum)
						)
					]
					[(eqv? (1st datum) 'set!)
						(set-exp (2nd datum) (parse-exp (3rd datum)))
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
					[(eqv? (1st datum) 'define)
						(define-exp (2nd datum) (parse-exp (3rd datum)))
					]
					[(eqv? (1st datum) 'exit-list)
						(exit-list-exp (inorder-map parse-exp (cdr datum)))
					]
					[else
						(app-exp
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
			[else
				(eopl:error 'parse-exp "Invalid concrete syntax ~s" datum)
			]
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

; Helper funtions to parse-exp lambda's w/ reference args
#|(define make-ref-args
	(lambda (ls)
		(cond
			[(null? ls) '()]
			[(list? (car ls)) (cons (car ls) (make-ref-args (cdr ls)))]
			[else (cons (list 'reg (car ls)) (make-ref-args (cdr ls)))]
		)
	)
) |#


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
		(extended-env-record syms (inorder-map box vals) env)))

#| (define extend-env-ref
	(lambda (vars args env)
		(extended-env-record vars
			(inorder-map (lambda (x) (if (box? x) x (box x))) args)
			env
		)
	)
) |#

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
	; succeed and fail are procedures applied if the var is or isn't found, respectively.
	(lambda (env sym succeed fail)
		(cases environment env
			(empty-env-record ()
				(fail))
			(extended-env-record (syms vals env)
				(let ([pos (list-find-position sym syms)])
					(if (number? pos)
						(succeed (list-ref vals pos))
						(apply-env env sym succeed fail)
					)
				)
			)
			(recursive-env-record (proc-names ids bodies old-env)
				(let ([pos (list-find-position sym proc-names)])
					(if (number? pos)
						(box (closure (list-ref ids pos) (list-ref bodies pos) env))
						(apply-env old-env sym succeed fail)
					)	
				)
			)
			(improper-recursive-env-record (proc-names ids bodies old-env)
				(let ([pos (list-find-position sym proc-names)])
					(if (number? pos)
						(let ([current-id (list-ref ids pos)])
							(if (list? current-id)
								(box (closure current-id (list-ref bodies pos) env))
								(box (improper-closure (flatten-improper-list current-id) (list-ref bodies pos) env))
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
				(app-exp (lambda-exp (list) (inorder-map syntax-expand bodies)) (list))
			]
			[cond-syn (conditions bodies)
				(if-exp (syntax-expand (car conditions)) 
						(syntax-expand (begin-syn (inorder-map syntax-expand (car bodies))))
						(if (null? (cdr conditions))
							(app-exp (var-exp 'void) '())
							(syntax-expand (cond-syn (cdr conditions) (cdr bodies)))
						)
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
					(syntax-expand
						(let-syn
							(list 'result)
							(list (syntax-expand (car bodies))) 
							(list
								(if-exp (var-exp 'result)
									(var-exp 'result)
									(if (null? (cdr bodies))
										(lit-exp #f)
										(syntax-expand (or-syn (cdr bodies)))
									)
								)
							)
						)
					)
				)
			]
			[let*-syn (vars vals bodies)
				(syntax-expand (let*-syn->let-syn vars vals bodies))
			]
			[named-let-syn (name vars vals bodies)
				(letrec-exp
					(list name)
					(list vars)
					(list (inorder-map syntax-expand bodies))
					(list
						(app-exp
							(var-exp name)
							(inorder-map syntax-expand vals)
						)
					)
				)
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
		#|	[ref-lambda-exp (args bodies)
				(ref-lambda-exp args (inorder-map syntax-expand bodies))
			] |#
			[exit-list-exp (args)
				(exit-list-exp (inorder-map syntax-expand args))
			]
			[if-exp (condition truecase falsecase)
				(if-exp (syntax-expand condition) (syntax-expand truecase) (syntax-expand falsecase))
			]
			[while-exp (condition bodies)
				(while-exp (syntax-expand condition) (inorder-map syntax-expand bodies))
			]
			[letrec-exp (proc-names ids bodies letrec-bodies)
				(letrec-exp
					proc-names
					ids
					(inorder-map (lambda (x) (inorder-map syntax-expand x)) bodies)
					(inorder-map syntax-expand letrec-bodies)
				)
			]
			[improper-letrec-exp (proc-names ids bodies letrec-bodies)
				(improper-letrec-exp
					proc-names
					ids
					(inorder-map (lambda (x) (inorder-map syntax-expand x)) bodies)
					(inorder-map syntax-expand letrec-bodies)
				)
			]
			[app-exp (rator rand)
				(app-exp (syntax-expand rator) (inorder-map syntax-expand rand))
			]
			[set-exp (id new-val)
				(set-exp id (syntax-expand new-val))
			]
			[define-exp (id new-val)
				(define-exp id (syntax-expand new-val))
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

; Helper functions for syntax-expand
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

; continuation datatype
(define-datatype continuation continuation?
	[init-k]
	[if-k
		(true-case expression?)
		(false-case expression?)
		(env environment?)
		(k continuation?)
	]
	[eval-rands-as-boxes-k
		(k continuation?)
	]
	[while-k 
		(loop procedure?)
		(bodies (list-of expression?))
		(x scheme-value?)
		(env environment?)
 		(k continuation?)
	]
	[while-loop-k 
		(loop procedure?)
		(k continuation?)
	]
	[inorder-map-k
		(proc procedure?)
		(cdr-lst list?)
		(k continuation?)
	]
	[inorder-map-cons-k
		(car-lst scheme-value?)
		(k continuation?)
	]
	[return-inorder-map-k 
		(proc procedure?)
		(cdr-lst list?)
		(k continuation?)
	]
	[rator-k 
		(rands (list-of expression?))
		(env environment?)
		(k continuation?)
	]
	[rands-k 
		(proc-value scheme-value?)
		(k continuation?)
	]
	[set!-k 
		(id symbol?)
		(env environment?)
		(k continuation?)
	]
	[define-k
		(id symbol?)
		(k continuation?)
	]
	[map-k 
		(loop procedure?)
		(proc proc-val?)
		(cdr-lst list?)
		(k continuation?)
	]
	[map-cons-k 
		(item scheme-value?)
		(k continuation?)
	]
)

; moves this up
(define apply-k
	(lambda (k val)
		(cases continuation k
			[init-k ()
				val
			]
			[if-k (true-case false-case env k)
				(if val
					(eval-exp true-case env k)
					(eval-exp false-case env k)
				)
			]
			;; NOT IN CPS
			[while-k (loop bodies x env k)
				(apply-k k 
					(if val
						(return-inorder-map-cps (lambda (body cont) (eval-exp body env cont)) bodies (while-loop-k loop k))
						(apply-k k x)
					)
				)
			]
			[while-loop-k (loop k)
				(loop val k)
			]
			[inorder-map-k (proc cdr-lst k)
				(inorder-map-cps
					proc 
					cdr-lst
					(inorder-map-cons-k val k)
				)
			]
			[inorder-map-cons-k (car-lst k)
				(apply-k k (cons car-lst val))
			]
			[return-inorder-map-k (proc cdr-lst k)
				(return-inorder-map-cps proc cdr-lst k)
			]
			[rator-k (rands env k)
				(eval-rands rands env (rands-k val k))
			]
			[eval-rands-as-boxes-k (k)
				(apply-k k (box val))
			]
			[rands-k (proc-value k)
				(apply-proc proc-value (inorder-map super-unbox val) k)
			]
			[set!-k (id env k)
				(apply-k k (set-box!
					(apply-env env id
						; procedure to call if id is in the environment 
						(lambda (x) x)
						; procedure to call if id not in env
						(lambda () (apply-env init-env id
							; procedure to call if id is in the environment 
							(lambda (x) x)
							; procedure to call if id not in env
							(lambda () (eopl:error 'apply-env "variable not found in environment: ~s" id)))
						)
					)
					val
				))
			]
			[define-k (id k)
				(apply-k k (let ([new-env (extend-env (list id) (list val) init-env)])
					(begin 
						(set! init-env new-env)
					)
				))
			]
			[map-k (loop proc cdr-list k)
				(loop proc cdr-list (map-cons-k val k))
			]
			[map-cons-k (item k)
				(apply-k k (cons item val))
			]
			
		)
	)
)

; top-level-eval evaluates a form in the global environment
(define top-level-eval
	(lambda (form)
		; later we may add things that are not expressions.
		(eval-exp form (empty-env) (init-k))))

; eval-exp is the main component of the interpreter
(define eval-exp
	(lambda (e env k)
		(cases expression e
			[lit-exp (datum) (apply-k k datum)]
			[var-exp (id)
				; look up its value.
				(apply-k k (super-unbox
					(apply-env env id
						; procedure to call if id is in the environment 
						(lambda (x) x)
						; procedure to call if id not in env
						(lambda () (apply-env init-env id
										; procedure to call if id is in the environment 
										(lambda (x) x)
										; procedure to call if id not in env
										(lambda () (eopl:error 'apply-env "variable not found in environment: ~s" id)))
						)
					)
				))
			]
			[exit-list-exp (args)
				(inorder-map-cps (lambda (x cont) (eval-exp x env cont)) args (init-k))
			]
			[if-exp (condition truecase falsecase)
				(eval-exp 
					condition 
					env 
					(if-k truecase falsecase env k)
				)
			]
			[lambda-exp (args bodies)
				(apply-k k (closure args bodies env))
			]
			[improper-lambda-exp (defined-args undefined-args bodies)
				; Simply makes a closure that has the undefined-args as the last variable
				(apply-k k (improper-closure (append defined-args (list undefined-args)) bodies env))
			]
		#|	[ref-lambda-exp (args bodies)
				(ref-closure args bodies env)
			] |#
			; TODO: NOT DONE
			[while-exp (condition bodies)
				(letrec ([loop (lambda (x cont)
									(eval-exp condition env (while-k loop bodies x env cont))
								) 
						])
						(loop '() k))
			
		#|		(let loop ([return '()])
						(if (eval-exp condition env)
							(loop (return-inorder-map (lambda (x) (eval-exp x env)) bodies))
							return
						)
				) |#
			]
			[letrec-exp (proc-names ids bodies letrec-bodies)
				(let ([new-env (recursive-env-record proc-names ids bodies env)])
					(return-inorder-map-cps (lambda (x cont) (eval-exp x new-env cont)) letrec-bodies k)
				)
			]
			[improper-letrec-exp (proc-names ids bodies letrec-bodies)
				(let ([new-env (improper-recursive-env-record proc-names ids bodies env)])
					(return-inorder-map-cps (lambda (x cont) (eval-exp x new-env cont)) letrec-bodies k)
				)
			]
			[app-exp (rator rands)
				(eval-exp
					rator
					env 
					(rator-k rands env k)
				)
			]
			[set-exp (id new-val)
				(eval-exp new-val env (set!-k id env k))
			
			]
			[define-exp (id new-val)
				(eval-exp new-val env (define-k id k))
			]
			[else (eopl:error 'eval-exp "Bad abstract syntax: ~a" e)]
		)
	)
)

; evaluate the list of operands, putting results into a list
(define eval-rands
	(lambda (rands env k)
		(inorder-map-cps (lambda (x cont) (eval-rands-as-boxes x env cont)) rands k)))
		
(define eval-rands-as-boxes
	(lambda (expression env k)
		(if (eqv? (car expression) 'var-exp)
			(apply-k k (apply-env 
				env 
				(cadr expression)
				; procedure to call if id is in the environment 
				(lambda (x) x)
				; procedure to call if id not in env
				(lambda () (apply-env 
								init-env 
								(cadr expression)
								; procedure to call if id is in the environment 
								(lambda (x) x)
								; procedure to call if id not in env
								(lambda () (eopl:error 'eval-rands-as-boxes "variable not found in environment: ~s" id))
							)
				)
			))
			(eval-exp 
				expression 
				env 
				(eval-rands-as-boxes-k k)
			)
		)
	)
)

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.
(define apply-proc
	(lambda (proc-value args k)
		(cases proc-val proc-value
			[prim-proc (op) (apply-prim-proc op (inorder-map super-unbox args) k)]
			[closure (vars body env) (apply-closure vars body env (inorder-map super-unbox args) k)]
			[improper-closure (vars body env) 
				(apply-closure vars body env (improper-closure-vals-init vars (inorder-map super-unbox args)) k)
			]
			[continuation-proc (k)
				(apply-k k (car args))
			]
		#|	[ref-closure (vars bodies env)
				(let ([indices (get-reg-indices vars)])
					(apply-ref-closure vars bodies env (unbox-the-things-we-need-to-unbox args indices))
				)
			] |#
			[else
				(eopl:error 'apply-proc "Attempt to apply bad procedure: ~s" proc-value)
			]
		)
	)
)
(define super-unbox
	(lambda (x)
		(if (box? x)
			(super-unbox (unbox x))
			x
		)
	)
)
					
(define apply-closure
	(lambda (vars bodies env args k)
		(let ([new-env (extend-env vars args env)])
			(return-inorder-map-cps (lambda (x cont) (eval-exp x new-env cont)) bodies k)
		)
	)
)

#| (define apply-ref-closure
	(lambda (vars bodies env args)
		(let* ([lst-vars (inorder-map cadr vars)] [new-env (extend-env-ref lst-vars args env)])
			(return-inorder-map (lambda (x) (eval-exp x new-env)) bodies)
		)
	)
) 

(define unbox-the-things-we-need-to-unbox
	(lambda (ls indices)
		(let loop ([ls ls] [indices indices] [index 0])
			(cond 
				[(null? indices) ls]
				[(= index (car indices))
					(cons
						(unbox (car ls))
						(loop (cdr ls) (cdr indices) (+ index 1))
					)

				]
				[else
					(cons
						(car ls)
						(loop (cdr ls) indices (+ index 1))
					)
				]
			)
		)
	)
)

(define get-reg-indices
	(lambda (ls)
		(let loop ([ls ls] [index 0])
			(cond
				[(null? ls) '()]
				[(eqv? (caar ls) 'reg) (cons index (loop (cdr ls) (+ 1 index)))]
				[else (loop (cdr ls) (+ 1 index))]
			)
		)
	)
) |#


; Prim procs and global env stuff
(define *prim-proc-names* '(+ - * / add1 sub1 cons = > < <= >= zero? not car cdr list null? assq eq? equal? atom? 
							length list->vector list? pair? procedure? vector->list vector make-vector vector-ref 
							vector? number? symbol? set-car! set-cdr! vector-set! display newline caar cadr 
							cdar cddr caaar caadr cadar cdaar caddr cdadr cddar cdddr quote void apply map memq quotient
							append eqv? list-tail call/cc))

(define init-env         ; for now, our initial global environment only contains 
	(extend-env            ; procedure names.  Recall that an environment associates
		*prim-proc-names*   ;  a value (not an expression) with an identifier.
		(inorder-map prim-proc *prim-proc-names*)
		(empty-env)
	)
)
			
(define global-env
	(extend-env
		*prim-proc-names*
		(inorder-map prim-proc *prim-proc-names*)
		(empty-env)
	)
)

(define reset-global-env
	(lambda ()
		(set! init-env global-env)
	)
)

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

; TODO: Change all of these to apply because :(
(define apply-prim-proc
	(lambda (prim-proc args k)
		(case prim-proc
			[(+) (apply-k k (apply + args))]
			[(-) (apply-k k (apply - args))]
			[(*) (apply-k k (apply * args))]
			[(/) (apply-k k (apply / args))]
			[(add1) (apply-k k (apply (lambda (x) (+ x 1)) args))]
			[(sub1) (apply-k k (apply (lambda (x) (- x 1)) args))]
			[(cons) (apply-k k (apply cons args))]
			[(=) (apply-k k (apply = args))]
			[(>) (apply-k k (apply > args))]
			[(<) (apply-k k (apply < args))]
			[(<=) (apply-k k (apply <= args))]
			[(>=) (apply-k k (apply >= args))]
			[(zero?) (apply-k k (apply zero? args))]
			[(not) (apply-k k (apply not args))]
			[(car) (apply-k k (apply car args))]
			[(cdr) (apply-k k (apply cdr args))]
			[(list) (apply-k k (apply list args))]
			[(null?) (apply-k k (apply null? args))]
			[(assq) (apply-k k (apply assq args))]
			[(eq?) (apply-k k (apply eq? args))]
			[(equal?) (apply-k k (apply equal? args))]
			[(atom?) (apply-k k (apply atom? args))]
			[(length) (apply-k k (apply length args))]
			[(list->vector) (apply-k k (list->vector (car args)))]
			[(list?) (apply-k k (list? (car args)))]
			[(pair?) (apply-k k (pair? (car args)))]
			[(procedure?) (apply-k k (proc-val? (car args)))]
			[(vector->list) (apply-k k (vector->list (car args)))]
			[(vector) (apply-k k (apply vector args))]
			[(vector-ref) (apply-k k (apply vector-ref args))]
			[(make-vector) (apply-k k (apply make-vector args))]
			[(caar) (apply-k k (apply caar args))]
			[(cadr) (apply-k k (apply cadr args))]
			[(cdar) (apply-k k (apply cdar args))]
			[(cddr) (apply-k k (apply cddr args))]
			[(caaar) (apply-k k (apply caaar args))]
			[(caadr) (apply-k k (apply caadr args))]
			[(cadar) (apply-k k (apply cadar args))]
			[(cdaar) (apply-k k (apply cdaar args))]
			[(caddr) (apply-k k (apply caddr args))]
			[(cddar) (apply-k k (apply cdaar args))]
			[(cdddr) (apply-k k (apply cdddr args))]
			[(cdadr) (apply-k k (apply cdadr args))]
			[(newline) (apply-k k (newline))]
			[(display) (apply-k k (begin (display (car args)) (newline)))]
			[(vector-set!) (apply-k k (apply vector-set! args))]
			[(set-cdr!) (apply-k k (apply set-cdr! args))]
			[(set-car!) (apply-k k (apply set-car! args))]
			[(symbol?) (apply-k k (apply symbol? args))]
			[(number?) (apply-k k (apply number? args))]
			[(vector?) (apply-k k (apply vector? args))]
			[(void) (apply-k k (void))]
			[(apply) (apply-proc (car args) (inorder-map box (cadr args)) k)]
			[(quote) (apply-k (quote (car args)))]
			[(map)
				(letrec ([loop (lambda (proc lst k)
									(if (null? lst)
										(apply-k k '())
										(apply-proc proc (inorder-map box (list (car lst))) (map-k loop proc (cdr lst) k))
									)
								)
						])
						(loop (car args) (cadr args) k)
				
				)
				
			#|	(let loop ([proc (car args)] [rest (cadr args)])
					(if (null? rest)
						'()
						(cons
							(apply-proc proc (inorder-map box (list (car rest))) k)
							(loop proc (cdr rest))
						)
					)
				) |#
			]
			[(memq) (apply-k k (apply memq args))]
			[(quotient) (apply-k k (apply quotient args))]
			[(append) (apply-k k (apply append args))]
			[(eqv?) (apply-k k (apply eqv? args))]
			[(list-tail) (apply-k k (apply list-tail args))]
			[(call/cc) (apply-proc (car args) (list (box (continuation-proc k))) k)]
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