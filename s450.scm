;;; file: s450.scm
;;;
;;; Metacircular evaluator from chapter 4 of STRUCTURE AND
;;; INTERPRETATION OF COMPUTER PROGRAMS (2nd edition)
;;;
;;; Modified by kwn, 3/4/97
;;; Modified and commented by Carl Offner, 10/21/98 -- 10/12/04
;;;
;;; This code is the code for the metacircular evaluator as it appears
;;; in the textbook in sections 4.1.1-4.1.4, with the following
;;; changes:
;;;
;;; 1.  It uses #f and #t, not false and true, to be Scheme-conformant.
;;;
;;; 2.  Some function names were changed to avoid conflict with the
;;; underlying Scheme:
;;;
;;;       eval => xeval
;;;       apply => xapply
;;;       extend-environment => xtend-environment
;;;
;;; 3.  The driver-loop is called s450.
;;;
;;; 4.  The booleans (#t and #f) are classified as self-evaluating.
;;;
;;; 5.  These modifications make it look more like UMB Scheme:
;;;
;;;        The define special form evaluates to (i.e., "returns") the
;;;          variable being defined.
;;;        No prefix is printed before an output value.
;;;
;;; 6.  I changed "compound-procedure" to "user-defined-procedure".
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 xeval and xapply -- the kernel of the metacircular evaluator
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;define a global variable the-dynamic environment
(define the-dynamic-environment '())

;;xeval first checks if a given type of expression is in special-form-table, if
;;it is in the special form table, the action corresponding to that special form
;;is invoked passing it the exp and env. If no action is found, check the rest
;;of the cond before returning an error.
(define (xeval exp env)
  (let ((action (lookup-action (type-of exp))))
    (if action
        (cond ((equal? text-of-quotation action) (action exp))
              ((equal? make-procedure action) (action (lambda-parameters exp)
                                               (lambda-body exp)
                                               env))
              ((equal? eval-sequence action) (action (begin-actions exp) env))
              ((equal? xeval action) (action (cond->if exp) env))
              (else (action exp env)))
        (cond ((self-evaluating? exp) exp)
              ((variable? exp) (lookup-variable-value exp env))
              ((application? exp)
               (let ((procedure (xeval (operator exp) env)));eval procedure
                 (let ((parameters (procedure-parameters procedure)));get proc args
                   (if (primitive-procedure? procedure)
                       (xapply procedure (list-of-values (operands exp) env))
                       ;;pass procedure to xapply and  pass parameters to check for
                       ;;special arguments (delayed) when evaluating arguments
                       (xapply procedure (list-of-values-overload parameters
                                                                  (operands exp)
                                                                  env))))))
              (else
               (s450Error "Unknown expression type -- XEVAL " exp))))))

(define (xapply procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((user-defined-procedure? procedure)
         ;;adjusted for dynamic, hold the return of xapply in a variable call
         ;;return, then pop the first frame off of the-dynamic-environmnet, and
         ;;return the evaluated value of xapply
         (let ((return (eval-sequence
                        (procedure-body procedure)
                        (xtend-environment
                         ;;loop through procedure parameters if encounter a
                         ;;pair as arg, meaning it is delayed reference or
                         ;;dynamic, need to just store the variable in frame
                         ;;without the tag.
                         (get-param (procedure-parameters procedure))
                         arguments
                         (procedure-environment procedure)))))
           (begin (set! the-dynamic-environment (cdr the-dynamic-environment))
           return)))
        (else
         (s450Error
          "Unknown procedure type -- XAPPLY " procedure))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;HANDLING OF SPECIAL ARGUMENTS (DELAYED, REFERENCE, DYNAMIC)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;DElAYED
;;original list of value
(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (xeval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

;;; Handling procedure arguments
;;check if formal argument is delayed before evaluating corresponding operand
(define (list-of-values-overload args exps env)
  (if (no-operands? exps)
      '()
      (if (pair? (car args))
          ;;check argument to see if delayed, create thunk obj
          (cond ((delayed? (car args)) (cons (make-thunk (first-operand exps) env)
                                             (list-of-values-overload
                                              (rest-arg args)
                                              (rest-operands exps)
                                              env)))
                ;;check argument to see if reference, create referral obj
                ((reference? (car args))
                 (if (symbol? (first-operand exps))
                     (cons (make-referral (first-operand exps) env)
                           (list-of-values-overload
                            (rest-arg args)
                            (rest-operands exps)
                            env))
                     (s450Error
                      "actual argument for reference must be a defined symbol")))
                ;;check argument to see if dynamic, evaluate exp in dynamic env
                ((dymanic? (car args)) (cons (xeval (first-operand exps)
                                                    the-dynamic-environment)
                                             (list-of-values-overload
                                              (rest-arg args)
                                              (rest-operands exps)
                                              env))))
          ;;normal evaluation
          (cons (xeval (first-operand exps) env)
                (list-of-values-overload (rest-arg args)
                                         (rest-operands exps)
                                         env)))))

;;formal argument list
(define (first-arg arguments) (car arguments))
(define (rest-arg arguments) (cdr arguments))

;;check if an argument is tagged with delayed
(define (delayed? arg)
  (tagged-list? arg 'delayed))

(define (thunk? arg)
  (tagged-list? arg 'thunk))

;;create thunk object with  unevaluated argument with env
(define (make-thunk operand env)
  (list 'thunk operand env))

;;in the case of an argument being a pair(delayed a), return just a itself
;;process a list of procedure parameters, used in xapply when extending environment
(define (get-param paramlist)
  (cond ((null? paramlist) '())
        ((pair? (car paramlist)) (cons (cadr (car paramlist))
                                       (get-param (cdr paramlist))))
        (else (cons (car paramlist) (get-param (cdr paramlist))))))


;;stream implementation
;;cons stream is a special form taking in exp and env as arg
;;when cons stream is called, the exp will be (cons-stream a b) where a is the car
;;and b is the promise(thunk, unevaluated). for a, we must evaluate so we call xeval
;;on a along with the environment and make a thunk with b and env to be evaluated
;;when needed
(define cons-stream
  (lambda (exp env)
    (cons (xeval (cadr exp) env) (list 'thunk (caddr exp) env))))

;;primitive stream-car is just the car of a stream
(define (stream-car strm)
  (car strm))

;;primitive stream-cdr is getting the cdr of a stream, and cdr of a stream is a thunk
;;so we must call xeval the cdr of stream to evaluate the content of the thunk
(define (stream-cdr strm)
  (xeval (cadr (cdr strm)) (caddr (cdr strm))))

(define the-empty-stream '())

(define (stream-null? strm)
  (equal? strm the-empty-stream)) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;REFERENCE

(define (reference? arg)
    (tagged-list? arg 'reference))
(define (referral? arg)
      (tagged-list? arg 'referral))

(define (make-referral operand env)
  (list 'referral operand env))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;DYNAMIC

(define (dymanic? arg)
  (tagged-list? arg 'dynamic))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These functions, called from xeval, do the work of evaluating some
;;; of the special forms:

(define (eval-if exp env)
  (if (true? (xeval (if-predicate exp) env))
      (xeval (if-consequent exp) env)
      (xeval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (xeval (first-exp exps) env))
        (else (xeval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

;;first check if name is in special-form-table before assignment
(define (eval-assignment exp env)
  (let ((name (assignment-variable exp)))
    (if (assoc name special-form-table);;check special-form-table
        (s450Error  "Cannot reassign special form: " name)
        (set-variable-value! name
                             (xeval (assignment-value exp) env)
                             env))
    name))    ;; A & S return 'ok

;;first check if name is in special-form-table before defining
(define (eval-definition exp env)
  (let ((name (definition-variable exp)))
    (if (assoc name special-form-table);;check special-form-table
        (s450Error  "Cannot redefine special form: " name)
        (define-variable! name
          (xeval (definition-value exp) env)
          env))
  name))     ;; A & S return 'ok

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Representing expressions
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Numbers, strings, and booleans are all represented as themselves.
;;; (Not characters though; they don't seem to work out as well
;;; because of an interaction with read and display.)

(define (self-evaluating? exp)
  (or (number? exp)
      (string? exp)
      (boolean? exp)
      ))

;;; variables -- represented as symbols

(define (variable? exp) (symbol? exp))

;;; quote -- represented as (quote <text-of-quotation>)

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp) (cadr exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

;;; assignment -- represented as (set! <var> <value>)

(define (assignment? exp) 
  (tagged-list? exp 'set!))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))

;;; definitions -- represented as
;;;    (define <var> <value>)
;;;  or
;;;    (define (<var> <parameter_1> <parameter_2> ... <parameter_n>) <body>)
;;;
;;; The second form is immediately turned into the equivalent lambda
;;; expression.

(define (definition? exp)
  (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

;;; lambda expressions -- represented as (lambda ...)
;;;
;;; That is, any list starting with lambda.  The list must have at
;;; least one other element, or an error will be generated.

(define (lambda? exp) (tagged-list? exp 'lambda))

(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

;;; conditionals -- (if <predicate> <consequent> <alternative>?)

(define (if? exp) (tagged-list? exp 'if))

(define (if-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      #f))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))


;;; sequences -- (begin <list of expressions>)

(define (begin? exp) (tagged-list? exp 'begin))

(define (begin-actions exp) (cdr exp))

(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))


;;; procedure applications -- any compound expression that is not one
;;; of the above expression types.

(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))


;;; Derived expressions -- the only one we include initially is cond,
;;; which is a special form that is syntactically transformed into a
;;; nest of if expressions.

(define (cond? exp) (tagged-list? exp 'cond))

(define (cond-clauses exp) (cdr exp))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      #f                          ; no else clause -- return #f
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (s450Error "ELSE clause isn't last -- COND->IF "
                       clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Truth values and procedure objects
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Truth values

(define (true? x)
  (not (eq? x #f)))

(define (false? x)
  (eq? x #f))


;;; Procedures

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (user-defined-procedure? p)
  (tagged-list? p 'procedure))


(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;problem 2. using a table to hold special form for xeval
;;create a 1d table to hold special form and create functions for the table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;table to hold special form each element is a pair where the car is the name of
;;a special form and the cdr is the action for that special form
(define special-form-table
  (list
   (list 'quote text-of-quotation)
   (list 'set! eval-assignment)
   (list 'define eval-definition)
   (list 'if eval-if)
   (list 'lambda make-procedure)
   (list 'begin eval-sequence)
   (list 'cond xeval)))

;;checks the type of expression given an expression as argument
(define (type-of exp)
  (if (pair? exp)
      (car exp)
      #f))

;;looks up a given type of expression from the special form table and return its
;;action
(define (lookup-action exp)
  (let ((record (assoc exp special-form-table)))
    (if record
        (cadr record)
        #f)))

;;install a new special form by passing it a name and action as argument. By
;;install, we are adding a pair to the special-form-table where the car of the
;;pair is name and cdr of the pair is action.
(define (install-special-form name action)
  (let ((var (assoc name special-form-table)))
    (if var
        (s450Error "special form already exist " name)
        (begin (set! special-form-table
                     (cons (list name action) special-form-table))
               name))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;problem 6 special form definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;takes a symbol as argument and returns true if the symbol is defined in the
;;current environment. implementation is the same as lookup-variable-value
;;except when variable is found we return true instead of the value. If not
;;found we return false instead of an error
(define (defined? exp env)
  (define (env-loop env)
    (define (scan vars)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? (cadr exp) (car vars))
             #t)
            (else (scan (cdr vars)))))
    (if (eq? env the-empty-environment)
        (let ((name (assoc (cadr exp) special-form-table)))
          (if name
              (begin (display "Special form: ") (car name))
              #f))
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)))))
    (env-loop env))

;;gets first frame of the environment, check if a variable is in that first
;;frame using member
(define locally-defined?
  (lambda (exp env)
    (let ((frame (first-frame env)))
      (if (member (cadr exp) (frame-variables frame))
          #t
          #f))))

;;starting with the first frame, check if symbol is in the first frame, if it is
;;then remove it by setting the variable to '() and its corresponding value to
;;'(). Then, call loop recursively with the rest of the frames and checking each
;;frame for the symbol and removing that symbol until all frames in the env is
;;processed.
(define make-unbound!
  (lambda (exp env)
    (let ((symbol (cadr exp)))
      (define (loop env)
        (if (equal? env the-empty-environment)
            'done
            (let ((frame (first-frame env)))
              (let ((vars (frame-variables frame))
                    (vals (frame-values frame)))
                (define (scan vars vals)
                  (cond ((null? vars) (loop (enclosing-environment env)))
                        ((equal? symbol (car vars))
                         (begin (set-car! vars '()) (set-car! vals '())
                                (loop (enclosing-environment env))))
                        (else (scan (cdr vars) (cdr vals)))))
                (scan vars vals)))))
      (loop env))))

;;scan goes through each variable and corresponding value of the first frame of
;;the env, checks to see if the variable match the symbol we want to remove, if
;;it match set that symbol remove that symbol and corresponding value by setting
;;them to '()
(define locally-make-unbound!
  (lambda (exp env)
    (let ((frame (first-frame env))
          (symbol (cadr exp)))
      (define (scan vars vals)
        (cond ((null? vars) 'done)
              ((equal? symbol (car vars))
               (begin (set-car! vars '()) (set-car! vals '()) 'done))
              (else (scan (cdr vars) (cdr vals)))))
      (scan (frame-variables frame) (frame-values frame)))))
              


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Representing environments
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; An environment is a list of frames.

(define (enclosing-environment env) (cdr env))

(define (first-frame env) (car env))

(define the-empty-environment '())

;;; Each frame is represented as a pair of lists:
;;;   1.  a list of the variables bound in that frame, and
;;;   2.  a list of the associated values.

(define (make-frame variables values)
  (cons variables values))

(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))

(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

;;; Extending an environment
;;for dynamic environment, we need to modify xtend-environment to add new frame
;;to the dynamic environment and also the base-environment, we still want the
;;keep the return value the same as before so we keep the cons statement as the
;;last statement of the begin expression
(define (xtend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (let ((newframe (make-frame vars vals)))
        (begin
          (set! the-dynamic-environment (cons newframe the-dynamic-environment))
          (cons newframe base-env)))
      (if (< (length vars) (length vals))
          (s450Error "Too many arguments supplied " vars vals)
          (s450Error "Too few arguments supplied " vars vals))))

;;; Looking up a variable in an environment
;;first check if the variable is a special form, is it is, output to prompt. if
;;not, search the environment for the variable
(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (let ((value (car vals)))
               ;;if value is thunk or referral object
               (if (or (thunk? value) (referral? value))
                   (xeval (cadr value) (caddr value));;evaluate the object
                   value)));;else return value
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (let ((name (assoc var special-form-table)))
          (if name
              (begin (display "Special form: ") (car name))
              (s450Error "Unbound variable " var)))
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

;;; Setting a variable to a new value in a specified environment.
;;; Note that it is an error if the variable is not already present
;;; (i.e., previously defined) in that environment.

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (if (referral? (car vals))
                 ;;referral object = ('referral exp env)
                 ;;set the referenced variable to val given the env from object
                 (set-variable-value! (cadr (car vals)) val (caddr (car vals)))
                 (set-car! vals val)))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (s450Error "Unbound variable -- SET! " var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

;;; Defining a (possibly new) variable.  First see if the variable
;;; already exists.  If it does, just change its value to the new
;;; value.  If it does not, define the new variable in the current
;;; frame.

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 The initial environment
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This is initialization code that is executed once, when the the
;;; interpreter is invoked.

(define (setup-environment)
  (let ((initial-env
         (xtend-environment '() '() the-empty-environment)))
    initial-env))

;;; Define the primitive procedures

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc) (cadr proc))

;;; Here is where we rely on the underlying Scheme implementation to
;;; know how to apply a primitive procedure.

(define (apply-primitive-procedure proc args)
  (apply (primitive-implementation proc) args))

;;install primitive procedures to s450 interpreter given a name and action check
;;to see if the name of the primitive procedure is a speial form if it is we
;;cannot install, else we install the primitive procedure by adding a new
;;binding to the first frame of the global environment with the variable being
;;the name and the value being the list ('primitive action). We need to make the
;;value being a list with the tag primitive since thats how the interpreter
;;identifies a primitive procedure
(define (install-primitive-procedure name action)
  (let ((var (assoc name special-form-table)))
    (if var
        (s450Error "cannot use name of a special form for name of a primitive" name)
        (begin (add-binding-to-frame! name
                                      (list 'primitive action)
                                      (first-frame the-global-environment))
               name))))
        

        
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 The main driver loop
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Note that (read) returns an internal representation of the next
;;; Scheme expression from the input stream.  It does NOT evaluate
;;; what is typed in -- it just parses it and returns an internal
;;; representation.  It is the job of the scheme evaluator to perform
;;; the evaluation.  In this case, our evaluator is called xeval.

(define input-prompt "s450==> ")
(define target '())
(define end '())

;;used for error handling and jumps to inside of s450 and prompt for user input
(define (s450Error . args)
  (begin (display args) (target 0)))

;;jumps to exit
(define (exit exp env)
  (end "exited s450"))

;;set the continuation at prompting user for input. also set another
;;continuation at outside the recursive call to (s450). The first continuation
;;is used for error handling within s450 and prompting back to start of s450 and
;;prompting user input. The second continuation is for when we want to skip
;;calling (s450) so we can exit s450.
(define (s450)
  (call/cc
   (lambda (here)
     (set! target here)))
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (call/cc
     (lambda (xyz)
       (set! end xyz)
       (if (eof-object? input)
           (end "exited s450"))
       (let ((output (xeval input the-global-environment)))
         (user-print output)
         (s450))))))

(define (prompt-for-input string)
  (newline) (newline) (display string))

;;; Note that we would not want to try to print a representation of the
;;; <procedure-env> below -- this would in general get us into an
;;; infinite loop.

(define (user-print object)
  (if (user-defined-procedure? object)
      (display (list 'user-defined-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Here we go:  define the global environment and invite the
;;;        user to run the evaluator.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define the-global-environment (setup-environment))

(display "... loaded the metacircular evaluator. (s450) runs it.")
(newline)

(define  the-dynamic-environment the-global-environment)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;using load to test install-special-form
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;action for load, used in s450 to load test files. s450=>(load "test.scm")
(define eval-load
  (lambda (exp env)
    (define (filename exp) (cadr exp))
    (define thunk (lambda ()
                    (readfile)
                    ))
    (define readfile (lambda()
                       (let ((item (read)))
                         (if (not (eof-object? item))
                             (begin
                               (xeval item env)
                               (readfile))))
                       ))
    (with-input-from-file (filename exp) thunk)
    (filename exp)      ; return the name of the file - why not?
        ))

;;install special form 'load
(install-special-form 'load eval-load)
(install-special-form 'defined? defined?)
(install-special-form 'locally-defined? locally-defined?)
(install-special-form 'locally-make-unbound! locally-make-unbound!)
(install-special-form 'make-unbound! make-unbound!)
(install-special-form 'exit exit)
(install-special-form 'cons-stream cons-stream)
;;install primitive procedures
(install-primitive-procedure 'car car)
(install-primitive-procedure 'cdr cdr)
(install-primitive-procedure 'cons cons)
(install-primitive-procedure 'null? null?)
(install-primitive-procedure 'equal? equal?)
(install-primitive-procedure '> >)
(install-primitive-procedure '< <)
(install-primitive-procedure '= =)
(install-primitive-procedure '+ +)
(install-primitive-procedure '- -)
(install-primitive-procedure '* *)
(install-primitive-procedure '/ /)
(install-primitive-procedure 'display display)
(install-primitive-procedure 'newline newline)
(install-primitive-procedure 'stream-car stream-car)
(install-primitive-procedure 'stream-cdr stream-cdr)
(install-primitive-procedure 'the-empty-stream the-empty-stream)
(install-primitive-procedure 'stream-null? stream-null?)
