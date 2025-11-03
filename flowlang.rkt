#lang racket

(require eopl
         racket/match
         racket/list
         racket/hash
         racket/string
         racket/format)

;; -----------------------------------------------------------------------------
;; Lexer and parser definitions using SLLGEN
;; -----------------------------------------------------------------------------

(define flowlang-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("//" (arbno (not #\newline))) skip)
    (number ((digit) (arbno digit)) number)
    (string ("\"" (arbno (not #\")) "\"") string)
    (keyword ("var" "const" "if" "else" "while" "do" "for" "foreach" "in" "return"
              "prototype" "func" "null" "verdadero" "falso" "ref" "deref" "setref"
              "this") keyword)
    (identifier ((or letter "_") (arbno (or letter digit "_" "-"))) symbol)))

(define flowlang-grammar
  '((program (statements) program)
    (statements ((arbno statement)) statements)

    (statement (var-decl) stmt-var)
    (statement (const-decl) stmt-const)
    (statement (assignment) stmt-assign)
    (statement (prototype-decl) stmt-proto)
    (statement (if-stmt) stmt-if)
    (statement (while-stmt) stmt-while)
    (statement (do-while-stmt) stmt-do-while)
    (statement (for-stmt) stmt-for)
    (statement (foreach-stmt) stmt-foreach)
    (statement (return-stmt) stmt-return)
    (statement (block) stmt-block)
    (statement (expr-stmt) stmt-expr)

    (var-decl ("var" identifier var-init ";") (var-decl $2 $3))
    (var-init () (var-no-init))
    (var-init (("=" expression)) (var-init $2))

    (const-decl ("const" identifier "=" expression ";") (const-decl $2 $4))

    (assignment (assign-target "=" expression ";") (assignment $1 $3))

    (assign-target (identifier) (assign-var $1))
    (assign-target (postfix-expression) (assign-postfix $1))

    (expr-stmt (expression ";") (expr-stmt $1))

    (prototype-decl ("prototype" identifier proto-parent "=" "{" proto-fields "}" ";")
                    (prototype-decl $2 $3 $6))
    (prototype-decl ("prototype" identifier proto-parent "{" proto-fields "}" ";")
                    (prototype-decl $2 $3 $5))

    (proto-parent () (proto-parent #f))
    (proto-parent ((":" identifier)) (proto-parent $2))

    (proto-fields () (proto-fields ()))
    (proto-fields ((proto-field (arbno (proto-field-sep proto-field))))
                  (proto-fields (cons $1 (map second $2))))
    (proto-field-sep (";"))
    (proto-field-sep (","))

    (proto-field (identifier ":" expression) (proto-field $1 $3))

    (block ("{" statements "}") (block $2))

    (if-stmt ("if" "(" expression ")" block else-clauses)
             (if-stmt $3 $5 $6))
    (else-clauses () (else-none))
    (else-clauses (("else" if-stmt)) (else-if $2))
    (else-clauses (("else" block)) (else-block $2))

    (while-stmt ("while" "(" expression ")" block) (while-stmt $3 $5))

    (do-while-stmt ("do" block "while" "(" expression ")" ";")
                   (do-while-stmt $2 $5))

    (for-stmt ("for" "(" for-init ";" opt-expression ";" opt-expression ")" block)
              (for-stmt $3 $5 $7 $9))
    (for-init () (for-none))
    (for-init ((var-decl-no-semi)) (for-init-var $1))
    (for-init ((expression)) (for-init-expr $1))
    (var-decl-no-semi ("var" identifier var-init)
                      (var-decl-ns $2 $3))

    (opt-expression () (opt-expr-none))
    (opt-expression ((expression)) (opt-expr $1))

    (foreach-stmt ("foreach" "(" foreach-binding "in" expression ")" block)
                  (foreach-stmt $3 $5 $7))
    (foreach-binding ("var" identifier) (foreach-var $2))
    (foreach-binding (identifier) (foreach-existing $1))

    (return-stmt ("return" return-expr ";") (return-stmt $2))
    (return-expr () (return-none))
    (return-expr ((expression)) (return-some $1))

    (expression (or-expression) (expr $1))

    (or-expression (or-expression "||" and-expression) (or-op $1 $3))
    (or-expression (and-expression) $1)

    (and-expression (and-expression "&&" equality-expression) (and-op $1 $3))
    (and-expression (equality-expression) $1)

    (equality-expression (equality-expression "==" relational-expression)
                         (eq-op $1 "==" $3))
    (equality-expression (equality-expression "!=" relational-expression)
                         (eq-op $1 "!=" $3))
    (equality-expression (relational-expression) $1)

    (relational-expression (relational-expression "<" additive-expression)
                           (rel-op $1 "<" $3))
    (relational-expression (relational-expression ">" additive-expression)
                           (rel-op $1 ">" $3))
    (relational-expression (relational-expression "<=" additive-expression)
                           (rel-op $1 "<=" $3))
    (relational-expression (relational-expression ">=" additive-expression)
                           (rel-op $1 ">=" $3))
    (relational-expression (additive-expression) $1)

    (additive-expression (additive-expression "+" multiplicative-expression)
                         (arith-op "+" $1 $3))
    (additive-expression (additive-expression "-" multiplicative-expression)
                         (arith-op "-" $1 $3))
    (additive-expression (multiplicative-expression) $1)

    (multiplicative-expression (multiplicative-expression "*" unary-expression)
                               (arith-op "*" $1 $3))
    (multiplicative-expression (multiplicative-expression "/" unary-expression)
                               (arith-op "/" $1 $3))
    (multiplicative-expression (multiplicative-expression "%" unary-expression)
                               (arith-op "%" $1 $3))
    (multiplicative-expression (unary-expression) $1)

    (unary-expression (("!" unary-expression)) (unary-op "!" $2))
    (unary-expression (("-" unary-expression)) (unary-op "-" $2))
    (unary-expression (postfix-expression) $1)

    (postfix-expression (postfix-expression "(" argument-list ")")
                        (call-expr $1 $3))
    (postfix-expression (postfix-expression "." identifier)
                        (prop-access $1 $3))
    (postfix-expression (postfix-expression "[" expression "]")
                        (index-access $1 $3))
    (postfix-expression (primary-expression) $1)

    (argument-list () (arg-list ()))
    (argument-list ((expression (arbno ("," expression))))
                   (arg-list (cons $1 (map second $2))))

    (primary-expression (identifier) (primary-id $1))
    (primary-expression (number) (primary-number $1))
    (primary-expression (string) (primary-string $1))
    (primary-expression ("verdadero") (primary-bool #t))
    (primary-expression ("falso") (primary-bool #f))
    (primary-expression ("null") (primary-null))
    (primary-expression ("(" expression ")") (primary-parens $2))
    (primary-expression (("ref" "(" expression ")")) (primary-ref $3))
    (primary-expression (("deref" "(" expression ")")) (primary-deref $3))
    (primary-expression (("setref" "(" expression "," expression ")"))
                        (primary-setref $3 $5))
    (primary-expression (list-literal) (primary-list $1))
    (primary-expression (dict-literal) (primary-dict $1))
    (primary-expression (func-literal) (primary-func $1))
    (primary-expression ("this") (primary-this))

    (list-literal ("[" opt-list-elements "]") (list-lit $2))
    (opt-list-elements () (list-elements ()))
    (opt-list-elements ((expression (arbno ("," expression))))
                       (list-elements (cons $1 (map second $2))))

    (dict-literal ("{" dict-entries "}" ) (dict-lit $2))
    (dict-entries () (dict-entries ()))
    (dict-entries ((dict-entry (arbno ("," dict-entry))))
                  (dict-entries (cons $1 (map second $2))))
    (dict-entry (string ":" expression) (dict-entry $1 $3))
    (dict-entry (identifier ":" expression) (dict-entry (symbol->string $1) $3))

    (func-literal ("func" "(" param-list ")" block)
                  (func-lit $3 $5))
    (param-list () (param-list ()))
    (param-list ((identifier (arbno ("," identifier))))
                (param-list (cons $1 (map second $2))))))

(define parse
  (sllgen:make-string-parser flowlang-lexical-spec flowlang-grammar))

;; -----------------------------------------------------------------------------
;; AST helpers
;; -----------------------------------------------------------------------------

(define (unwrap-ast ast)
  (match ast
    [(list 'program statements) statements]
    [_ ast]))

;; -----------------------------------------------------------------------------
;; Runtime structures
;; -----------------------------------------------------------------------------

(struct binding (box mutable?) #:transparent)

(define (make-env)
  (list (make-hash)))

(define (push-scope env)
  (cons (make-hash) env))

(define (lookup-binding env name)
  (let loop ((frames env))
    (cond
      [(null? frames)
       (error 'lookup (format "Identificador no definido: ~a" name))]
      [else
       (define frame (car frames))
       (define b (hash-ref frame name #f))
       (if b b (loop (cdr frames)))])))

(define (define-binding! env name value mutable?)
  (define frame (car env))
  (when (hash-has-key? frame name)
    (error 'define (format "Identificador redefinido en el mismo alcance: ~a" name)))
  (hash-set! frame name (binding (box value) mutable?)))

(define (set-binding! env name value)
  (define b (lookup-binding env name))
  (unless (binding-mutable? b)
    (error 'set (format "Intento de modificar constante: ~a" name)))
  (set-box! (binding-box b) value)
  value)

(define (get-binding-value env name)
  (unbox (binding-box (lookup-binding env name))))

(struct closure (params body env) #:transparent)
(struct bound-closure (closure this) #:transparent)
(struct prototype (name parent fields) #:transparent)
(struct proto-entry (name expr env) #:transparent)
(struct object (fields prototype) #:transparent)

;; store for prototypes defined by name
(define prototype-table (make-hash))

;; -----------------------------------------------------------------------------
;; Evaluation helpers
;; -----------------------------------------------------------------------------

(struct return-signal (value) #:transparent)

(define (signal-return value)
  (return-signal value))

(define (flowlang-null) 'null)

(define (truthy? v)
  (cond
    [(eq? v 'null) #f]
    [(boolean? v) v]
    [else (not (equal? v #f))]))

(define (ensure-number v who)
  (unless (number? v)
    (error who "Se esperaba un numero"))
  v)

(define (ensure-integer-index v who)
  (ensure-number v who)
  (cond
    [(integer? v) (inexact->exact v)]
    [else (error who "El indice debe ser un entero" )]))

(define (ensure-boolean v who)
  (unless (boolean? v)
    (error who "Se esperaba un booleano"))
  v)

(define (ensure-list v who)
  (unless (list? v)
    (error who "Se esperaba una lista"))
  v)

(define (ensure-dict v who)
  (unless (hash? v)
    (error who "Se esperaba un diccionario"))
  v)

(define (ensure-object v who)
  (unless (object? v)
    (error who "Se esperaba un objeto"))
  v)

;; -----------------------------------------------------------------------------
;; Evaluation of AST
;; -----------------------------------------------------------------------------

(define (eval-program parsed)
  (define env (make-env))
  (initialize-builtins! env)
  (eval-statements parsed env))

(define (eval-statements ast env)
  (match ast
    [(list 'statements stmts)
     (eval-statement-list stmts env)]
    [_ (error 'eval "AST desconocido para statements: ~a" ast)]))

(define (eval-statement-list stmts env)
  (define (loop lst last-val)
    (if (null? lst)
        last-val
        (let ((result (eval-statement (car lst) env)))
          (if (return-signal? result)
              result
              (loop (cdr lst) result)))))
  (loop stmts (flowlang-null)))

(define (eval-statement stmt env)
  (match stmt
    [(list 'stmt-var var-decl) (eval-var-decl var-decl env)]
    [(list 'stmt-const const-decl) (eval-const-decl const-decl env)]
    [(list 'stmt-assign assignment) (eval-assignment assignment env)]
    [(list 'stmt-proto proto) (eval-prototype-decl proto env)]
    [(list 'stmt-if ifstmt) (eval-if-stmt ifstmt env)]
    [(list 'stmt-while whilestmt) (eval-while-stmt whilestmt env)]
    [(list 'stmt-do-while do-while) (eval-do-while-stmt do-while env)]
    [(list 'stmt-for forstmt) (eval-for-stmt forstmt env)]
    [(list 'stmt-foreach foreach) (eval-foreach-stmt foreach env)]
    [(list 'stmt-return return) (eval-return-stmt return env)]
    [(list 'stmt-block block) (eval-block block env)]
    [(list 'stmt-expr expr-stmt) (eval-expression-stmt expr-stmt env)]
    [_ (error 'eval-statement (format "Tipo de sentencia no soportado: ~a" stmt))]))

(define (eval-var-decl ast env)
  (match ast
    [(list 'var-decl name (list 'var-no-init))
     (define-binding! env name (flowlang-null) #t)
     (flowlang-null)]
    [(list 'var-decl name (list 'var-init expr))
     (define value (eval-expression expr env))
     (define-binding! env name value #t)
     value]))

(define (eval-const-decl ast env)
  (match ast
    [(list 'const-decl name expr)
     (define value (eval-expression expr env))
     (define-binding! env name value #f)
     value]))

(define (eval-assignment ast env)
  (match ast
    [(list 'assignment target expr)
     (define value (eval-expression expr env))
     (assign-target! target value env)
     value]))

(define (assign-target! target value env)
  (match target
    [(list 'assign-var name)
     (set-binding! env name value)]
    [(list 'assign-postfix postfix)
     (assign-postfix! postfix value env)]
    [_ (error 'assign-target! "Destino de asignacion no soportado")]))

(define (assign-postfix! postfix value env)
  (match postfix
    [(list 'prop-access obj-expr name)
     (define obj (eval-postfix obj-expr env))
     (set-object-property! obj name value)
     value]
    [(list 'index-access target index-expr)
     (define container (eval-postfix target env))
     (define index (eval-expression index-expr env))
     (cond
       [(list? container)
        (define idx (ensure-integer-index index 'asignar-indice))
        (unless (and (integer? idx) (<= 0 idx) (< idx (length container)))
          (error 'asignar-indice "Indice fuera de rango"))
        (define new-list (list-set container idx value))
        (assign-postfix-helper target new-list env)
        value]
       [(hash? container)
        (assign-postfix-helper target (hash-set container index value) env)
        value]
       [else
        (error 'assign-postfix! "Indice solo permitido en listas o diccionarios")])]
    [_ (error 'assign-postfix! "Destino postfix no soportado"))]))

(define (assign-postfix-helper target new-value env)
  (match target
    [(list 'primary-id name)
     (set-binding! env name new-value)]
    [(list 'prop-access obj-expr name)
     (define obj (eval-postfix obj-expr env))
     (set-object-property! obj name new-value)]
    [(list 'index-access inner idx)
     (define container (eval-postfix inner env))
     (define index (eval-expression idx env))
     (cond
       [(list? container)
        (define idxn (ensure-integer-index index 'asignar-indice))
        (unless (and (integer? idxn) (<= 0 idxn) (< idxn (length container)))
          (error 'asignar-indice "Indice fuera de rango"))
        (assign-postfix-helper inner (list-set container idxn new-value) env)]
       [(hash? container)
        (assign-postfix-helper inner (hash-set container index new-value) env)]
       [else
        (error 'assign-postfix-helper "Destino de asignacion invalido")])]
    [_ (error 'assign-postfix-helper "Asignacion no soportada"))]))

(define (eval-expression-stmt ast env)
  (match ast
    [(list 'expr-stmt expr)
     (eval-expression expr env)]))

(define (eval-block ast env)
  (match ast
    [(list 'block statements)
     (define new-env (push-scope env))
     (define result (eval-statements statements new-env))
     (if (return-signal? result) result result)]))

(define (eval-if-stmt ast env)
  (match ast
    [(list 'if-stmt cond block else-branch)
     (if (truthy? (eval-expression cond env))
         (eval-block block env)
         (eval-else else-branch env))]))

(define (eval-else ast env)
  (match ast
    [(list 'else-none) (flowlang-null)]
    [(list 'else-block block) (eval-block block env)]
    [(list 'else-if ifstmt) (eval-if-stmt ifstmt env)]
    [_ (flowlang-null)]))

(define (eval-while-stmt ast env)
  (match ast
    [(list 'while-stmt cond block)
     (let loop ()
       (if (truthy? (eval-expression cond env))
           (let ([result (eval-block block env)])
             (if (return-signal? result)
                 result
                 (loop)))
           (flowlang-null)))]))

(define (eval-do-while-stmt ast env)
  (match ast
    [(list 'do-while-stmt block cond)
     (let loop ()
       (let ([result (eval-block block env)])
         (cond
           [(return-signal? result) result]
           [(truthy? (eval-expression cond env)) (loop)]
           [else (flowlang-null)])))]))

(define (eval-for-stmt ast env)
  (match ast
    [(list 'for-stmt init cond update block)
     (define loop-env (push-scope env))
     (eval-for-init init loop-env)
     (let loop ()
       (if (truthy? (eval-opt-expr cond loop-env))
           (let ([result (eval-block block loop-env)])
             (if (return-signal? result)
                 result
                 (begin
                   (eval-opt-expr update loop-env)
                   (loop))))
           (flowlang-null)))]))

(define (eval-for-init init env)
  (match init
    [(list 'for-none) (flowlang-null)]
    [(list 'for-init-var (list 'var-decl-ns name (list 'var-no-init)))
     (define-binding! env name (flowlang-null) #t)]
    [(list 'for-init-var (list 'var-decl-ns name (list 'var-init expr)))
     (define value (eval-expression expr env))
     (define-binding! env name value #t)]
    [(list 'for-init-expr expr) (eval-expression expr env)]
    [_ (flowlang-null)]))

(define (eval-opt-expr opt env)
  (match opt
    [(list 'opt-expr-none) #t]
    [(list 'opt-expr expr) (eval-expression expr env)]))

(define (eval-foreach-stmt ast env)
  (match ast
    [(list 'foreach-stmt binding collection block)
     (define coll (eval-expression collection env))
     (cond
       [(list? coll)
        (let loop ([items coll])
          (if (null? items)
              (flowlang-null)
              (let* ([foreach-env (push-scope env)]
                     [_ (bind-foreach binding (car items) foreach-env env)]
                     [result (eval-block block foreach-env)])
                (if (return-signal? result)
                    result
                    (loop (cdr items))))))]
       [(hash? coll)
        (let loop ([pairs (hash->list coll)])
          (if (null? pairs)
              (flowlang-null)
              (let* ([foreach-env (push-scope env)]
                     [_ (bind-foreach binding (car pairs) foreach-env env)]
                     [result (eval-block block foreach-env)])
                (if (return-signal? result)
                    result
                    (loop (cdr pairs))))))]
       [else (error 'foreach "Coleccion invalida en foreach")])
     (define result
       (cond
         [(list? coll)
          (let loop ([items coll])
            (if (null? items)
                (flowlang-null)
                (let* ([foreach-env (push-scope env)]
                       [_ (bind-foreach binding (car items) foreach-env env)]
                       [loop-result (eval-block block foreach-env)])
                  (if (return-signal? loop-result)
                      loop-result
                      (loop (cdr items))))))]
         [(hash? coll)
          (let loop ([pairs (hash->list coll)])
            (if (null? pairs)
                (flowlang-null)
                (let* ([foreach-env (push-scope env)]
                       [_ (bind-foreach binding (car pairs) foreach-env env)]
                       [loop-result (eval-block block foreach-env)])
                  (if (return-signal? loop-result)
                      loop-result
                      (loop (cdr pairs))))))]
         [else (error 'foreach "Coleccion invalida en foreach")]))
     (if (return-signal? result) result (flowlang-null))]))

(define (bind-foreach binding value inner-env outer-env)
  (match binding
    [(list 'foreach-var name)
     (define-binding! inner-env name value #t)]
    [(list 'foreach-existing name)
     (set-binding! outer-env name value)]))

(define (eval-return-stmt ast env)
  (match ast
    [(list 'return-stmt (list 'return-none))
     (signal-return (flowlang-null))]
    [(list 'return-stmt (list 'return-some expr))
     (signal-return (eval-expression expr env))]))

(define (eval-expression ast env)
  (match ast
    [(list 'expr expr) (eval-or expr env)]
    [_ (eval-or ast env)]))

(define (eval-or ast env)
  (match ast
    [(list 'or-op left right)
     (if (truthy? (eval-or left env))
         #t
         (truthy? (eval-or right env)))]
    [_ (eval-and ast env)]))

(define (eval-and ast env)
  (match ast
    [(list 'and-op left right)
     (if (truthy? (eval-and left env))
         (truthy? (eval-and right env))
         #f)]
    [_ (eval-equality ast env)]))

(define (eval-equality ast env)
  (match ast
    [(list 'eq-op left op right)
     (define lv (eval-equality left env))
     (define rv (eval-relational right env))
     (case op
       [("==") (boolean (equal? lv rv))]
       [("!=") (boolean (not (equal? lv rv)))]
       [else (error 'eq-op "Operador de igualdad desconocido")]))]
    [_ (eval-relational ast env)]))

(define (boolean v) (if v #t #f))

(define (eval-relational ast env)
  (match ast
    [(list 'rel-op left op right)
     (define lv (eval-relational left env))
     (define rv (eval-additive right env))
     (ensure-number lv 'rel-op)
     (ensure-number rv 'rel-op)
     (case op
       [("<") (boolean (< lv rv))]
       [(">") (boolean (> lv rv))]
       [("<=") (boolean (<= lv rv))]
       [(">=") (boolean (>= lv rv))]
       [else (error 'rel-op "Operador relacional desconocido")]))]
    [_ (eval-additive ast env)]))

(define (eval-additive ast env)
  (match ast
    [(list 'arith-op op left right)
     (define lv (eval-additive left env))
     (define rv (eval-multiplicative right env))
     (case op
       [("+") (eval-plus lv rv)]
       [("-") (binary-number op lv rv)]
       [else (error 'additive "Operador no soportado"))])]
    [_ (eval-multiplicative ast env)]))

(define (eval-plus lv rv)
  (cond
    [(and (number? lv) (number? rv)) (+ lv rv)]
    [(and (string? lv) (string? rv)) (string-append lv rv)]
    [(and (list? lv) (list? rv)) (append lv rv)]
    [else (error '+ "Tipos incompatibles para +")]))

(define (binary-number op lv rv)
  (ensure-number lv op)
  (ensure-number rv op)
  (case op
    [("-") (- lv rv)]
    [("*") (* lv rv)]
    [("/") (/ lv rv)]
    [("%") (remainder lv rv)]
    [else (error 'binary-number "Operador desconocido")]))

(define (eval-multiplicative ast env)
  (match ast
    [(list 'arith-op op left right)
     (define lv (eval-multiplicative left env))
     (define rv (eval-unary right env))
     (binary-number op lv rv)]
    [_ (eval-unary ast env)]))

(define (eval-unary ast env)
  (match ast
    [(list 'unary-op op expr)
     (define value (eval-unary expr env))
     (case op
       [("-") (- (ensure-number value 'unary))]
       [("!") (boolean (not (truthy? value)))]
       [else (error 'unary "Operador unario desconocido")]))]
    [_ (eval-postfix ast env)]))

(define (eval-postfix ast env)
  (match ast
    [(list 'call-expr target args)
     (define proc (eval-postfix target env))
     (define arg-values (map (lambda (a) (eval-expression a env)) (extract-args args)))
     (apply-procedure proc arg-values)]
    [(list 'prop-access target name)
     (define obj (eval-postfix target env))
     (lookup-property obj name)]
    [(list 'index-access target expr)
     (define container (eval-postfix target env))
     (define idx (eval-expression expr env))
     (cond
       [(list? container)
        (define i (ensure-integer-index idx 'index))
        (unless (and (integer? i) (<= 0 i) (< i (length container)))
          (error 'index "Indice fuera de rango"))
        (list-ref container i)]
       [(hash? container)
        (hash-ref container idx (lambda () (flowlang-null)))]
       [else (error 'index "Indexacion invalida")])]
    [(list 'primary-id name)
     (get-binding-value env name)]
    [(list 'primary-number n) n]
    [(list 'primary-string s) s]
    [(list 'primary-bool b) b]
    [(list 'primary-null) (flowlang-null)]
    [(list 'primary-parens expr) (eval-expression expr env)]
    [(list 'primary-ref expr) (box (eval-expression expr env))]
    [(list 'primary-deref expr)
     (define ref (eval-expression expr env))
     (if (box? ref) (unbox ref) (error 'deref "Se esperaba referencia"))]
    [(list 'primary-setref ref-expr value-expr)
     (define ref (eval-expression ref-expr env))
     (define value (eval-expression value-expr env))
     (if (box? ref)
         (begin (set-box! ref value) value)
         (error 'setref "Se esperaba referencia"))]
    [(list 'primary-list elements)
     (map (lambda (expr) (eval-expression expr env)) (extract-list-elements elements))]
    [(list 'primary-dict entries)
     (let ((result (make-hash)))
       (for ([entry (extract-dict-entries entries)])
         (define key (first entry))
         (define value (eval-expression (second entry) env))
         (hash-set! result key value))
       result)]
    [(list 'primary-func func) (eval-func-literal func env)]
    [(list 'primary-this)
     (get-binding-value env 'this)]
    [_ (error 'eval-postfix (format "Postfix no soportado: ~a" ast))]))

(define (extract-args ast)
  (match ast
    [(list 'arg-list args) args]
    [_ '()]))

(define (extract-list-elements ast)
  (match ast
    [(list 'list-elements elems) elems]
    [_ '()]))

(define (extract-dict-entries ast)
  (match ast
    [(list 'dict-entries entries) entries]
    [_ '()]))

(define (eval-func-literal ast env)
  (match ast
    [(list 'func-lit params block)
     (closure (extract-params params) block env)]))

(define (extract-params ast)
  (match ast
    [(list 'param-list params) params]
    [_ '()]))

(define (apply-procedure proc args)
  (cond
    [(closure? proc) (invoke-closure proc args #f)]
    [(bound-closure? proc)
     (invoke-closure (bound-closure-closure proc) args (bound-closure-this proc))]
    [(procedure? proc) (apply proc args)]
    [else (error 'apply "Valor no invocable: ~a" proc)]))

(define (invoke-closure clos args this-value)
  (define params (closure-params clos))
  (when (not (= (length params) (length args)))
    (error 'invoke "Numero incorrecto de argumentos"))
  (define new-env (push-scope (closure-env clos)))
  (for ([p params] [a args])
    (define-binding! new-env p a #t))
  (when this-value
    (define-binding! new-env 'this this-value #f))
  (define result (eval-block (closure-body clos) new-env))
  (if (return-signal? result)
      (return-signal-value result)
      result))

(define (lookup-property obj name)
  (cond
    [(object? obj) (lookup-object-property obj name)]
    [(prototype? obj) (lookup-prototype-property obj name)]
    [else (error 'prop "Acceso a propiedad sobre valor no objeto")]))

(define (lookup-object-property obj name)
  (define fields (object-fields obj))
  (if (hash-has-key? fields name)
      (bind-if-closure (hash-ref fields name) obj)
      (if (object-prototype obj)
          (lookup-prototype-property (object-prototype obj) name obj)
          (error 'prop (format "Propiedad no definida: ~a" name)))))

(define (lookup-prototype-property proto name [instance #f])
  (define field
    (for/or ([entry (prototype-fields proto)])
      (and (eq? (proto-entry-name entry) name) entry)))
  (cond
    [field
     (bind-if-closure (proto-entry-value field) instance)]
    [(prototype-parent proto)
     (lookup-prototype-property (prototype-parent proto) name instance)]
    [else (error 'prop (format "Propiedad no definida: ~a" name))]))

(define (proto-entry-value field)
  (eval-expression (proto-entry-expr field) (proto-entry-env field)))

(define (bind-if-closure value instance)
  (cond
    [(closure? value) (if instance
                          (bound-closure value instance)
                          value)]
    [else value]))

(define (set-object-property! obj name value)
  (unless (object? obj)
    (error 'prop "Solo se puede asignar propiedades en objetos"))
  (hash-set! (object-fields obj) name value))

(define (eval-prototype-decl ast env)
  (match ast
    [(list 'prototype-decl name (list 'proto-parent parent-name) fields)
     (define parent (if parent-name
                        (hash-ref prototype-table parent-name #f)
                        #f))
     (unless (or (not parent-name) parent)
       (error 'prototype (format "Prototipo padre no encontrado: ~a" parent-name)))
  (define proto
       (prototype name parent (map (lambda (field)
                                     (match field
                                       [(list 'proto-field fname expr)
                                        (proto-entry fname expr env)]))
                                   (extract-proto-fields fields))))
     (hash-set! prototype-table name proto)
     (define-binding! env name proto #f)
     proto]))

(define (extract-proto-fields ast)
  (match ast
    [(list 'proto-fields fields) fields]
    [_ '()]))

(define (create-object proto)
  (unless (prototype? proto)
    (error 'crear "Se esperaba un prototipo"))
  (object (instantiate-prototype-fields proto) proto))

(define (instantiate-prototype-fields proto)
  (define base
    (if (prototype-parent proto)
        (hash-copy (instantiate-prototype-fields (prototype-parent proto)))
        (make-hash)))
  (for ([field (prototype-fields proto)])
    (hash-set! base (proto-entry-name field)
               (eval-expression (proto-entry-expr field) (proto-entry-env field))))
  base)

(define (lookup-object-property-from-prototype proto name instance)
  (lookup-prototype-property proto name instance))

(define (flowlang-print . args)
  (for ([a args])
    (display (value->string a)))
  (newline)
  (flowlang-null))

(define (value->string v)
  (cond
    [(eq? v (flowlang-null)) "null"]
    [(boolean? v) (if v "verdadero" "falso")]
    [(number? v) (number->string v)]
    [(string? v) v]
    [(list? v) (format "[~a]" (string-join (map value->string v) ", "))]
    [(hash? v)
     (format "{~a}" (string-join (map (lambda (pair)
                                         (format "~a: ~a" (value->string (car pair))
                                                 (value->string (cdr pair))))
                                       (hash->list v)) ", "))]
    [(object? v) "<objeto>"]
    [(prototype? v) (format "<prototipo ~a>" (prototype-name v))]
    [(closure? v) "<funcion>"]
    [(bound-closure? v) "<metodo>"]
    [else (format "~a" v)]))

;; Builtin functions -----------------------------------------------------------

(define (initialize-builtins! env)
  (define-binding! env 'print flowlang-print #f)
  (define-binding! env 'crear create-object #f)
  (define-binding! env 'longitud longitud-builtin #f)
  (define-binding! env 'agregar agregar-builtin #f)
  (define-binding! env 'vacia? vacia?-builtin #f)
  (define-binding! env 'cabeza cabeza-builtin #f)
  (define-binding! env 'cola cola-builtin #f)
  (define-binding! env 'obtener obtener-builtin #f)
  (define-binding! env 'colocar colocar-builtin #f)
  (define-binding! env 'append append-builtin #f)
  (define-binding! env 'crear-lista crear-lista-builtin #f)
  (define-binding! env 'crear-diccionario crear-diccionario-builtin #f)
  (define-binding! env 'claves claves-builtin #f)
  (define-binding! env 'valores valores-builtin #f)
  (define-binding! env 'contiene? contiene?-builtin #f)
  (define-binding! env 'clonar clonar-builtin #f)
  (define-binding! env 'mapa mapa-builtin #f)
  (define-binding! env 'filtrar filtrar-builtin #f)
  (define-binding! env 'reducir reducir-builtin #f)
  (define-binding! env 'iterar iterar-builtin #f)
  (define-binding! env 'begin begin-builtin #f))

(define (longitud-builtin value)
  (cond
    [(string? value) (string-length value)]
    [(list? value) (length value)]
    [(hash? value) (hash-count value)]
    [else (error 'longitud "Valor sin longitud")]))

(define (agregar-builtin lst value)
  (ensure-list lst 'agregar)
  (append lst (list value)))

(define (vacia?-builtin lst)
  (ensure-list lst 'vacia?)
  (boolean (null? lst)))

(define (cabeza-builtin lst)
  (ensure-list lst 'cabeza)
  (if (null? lst)
      (error 'cabeza "Lista vacia")
      (car lst)))

(define (cola-builtin lst)
  (ensure-list lst 'cola)
  (if (null? lst)
      '()
      (cdr lst)))

(define (obtener-builtin collection key)
  (cond
    [(list? collection)
     (define idx (ensure-integer-index key 'obtener))
     (unless (and (integer? idx) (<= 0 idx) (< idx (length collection)))
       (error 'obtener "Indice fuera de rango"))
     (list-ref collection idx)]
    [(hash? collection)
     (hash-ref collection key (lambda () (flowlang-null)))]
    [else (error 'obtener "Coleccion invalida"))])

(define (colocar-builtin collection key value)
  (cond
    [(list? collection)
     (define idx (ensure-integer-index key 'colocar))
     (unless (and (integer? idx) (<= 0 idx) (< idx (length collection)))
       (error 'colocar "Indice fuera de rango"))
     (list-set collection idx value)]
    [(hash? collection)
     (hash-set collection key value)]
    [else (error 'colocar "Coleccion invalida"))])

(define (append-builtin lst1 lst2)
  (ensure-list lst1 'append)
  (ensure-list lst2 'append)
  (append lst1 lst2))

(define (crear-lista-builtin . args)
  args)

(define (crear-diccionario-builtin . args)
  (define result (make-hash))
  (cond
    [(and (not (null? args))
          (andmap (lambda (item) (and (list? item) (= (length item) 2))) args))
     (for ([pair args])
       (hash-set! result (first pair) (second pair)))]
    [(even? (length args))
     (for ([i (in-range 0 (length args) 2)])
       (hash-set! result (list-ref args i)
                  (list-ref args (add1 i))))]
    [else
     (error 'crear-diccionario "Argumentos invalidos"))]
  result)

(define (claves-builtin dict)
  (hash-keys (ensure-dict dict 'claves)))

(define (valores-builtin dict)
  (hash-values (ensure-dict dict 'valores)))

(define (contiene?-builtin dict key)
  (boolean (hash-has-key? (ensure-dict dict 'contiene?) key)))

(define (clonar-builtin obj)
  (cond
    [(object? obj)
     (object (hash-copy (object-fields obj)) (object-prototype obj))]
    [else (error 'clonar "Solo se pueden clonar objetos instanciados")]))

(define (mapa-builtin func lst)
  (ensure-list lst 'mapa)
  (map (lambda (item) (apply-procedure func (list item))) lst))

(define (filtrar-builtin func lst)
  (ensure-list lst 'filtrar)
  (filter (lambda (item) (truthy? (apply-procedure func (list item)))) lst))

(define (reducir-builtin func lst inicial)
  (ensure-list lst 'reducir)
  (foldl (lambda (item acc) (apply-procedure func (list acc item))) inicial lst))

(define (iterar-builtin func lst)
  (ensure-list lst 'iterar)
  (for-each (lambda (item) (apply-procedure func (list item))) lst)
  (flowlang-null))

(define (begin-builtin . exprs)
  (if (null? exprs)
      (flowlang-null)
      (car (reverse exprs))))

;; -----------------------------------------------------------------------------
;; Entry point convenience
;; -----------------------------------------------------------------------------

(define (run source)
  (define parsed (unwrap-ast (parse source)))
  (eval-program parsed))

(provide run parse)
