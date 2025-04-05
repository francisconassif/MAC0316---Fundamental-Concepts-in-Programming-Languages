#lang plai-typed

#|
 | EP#01 - MAC0316 - Conceitos Fundamentais de Linguagens de Programação
 | Professor:   Alan Mitchell Durham
 | Aluno:       Francisco Membrive
 | Data:        21/10/2024
 | Objetivo:    Incrementar o interpretador disponibilizado com let, let*, letrec,
 |              quote e read-loop
 |              Em cada seção do código, as operações adicionadas ficaram na sub-
 |              seção "Adicionadas".
 |              Os comentários originais foram mantidos.
 |              Comentei as linhas do read-loop pois estavam gerando bad syntax
 |              e impedindo de rodar o código.
 |#


#|
 | interpretador simples, sem variáveis ou funçõess
 |#

#| primeiro as expressões "primitivas", ou seja, diretamente interpretadas
 |#

(define-type ExprC
  [numC    (n : number)]
  [idC     (s : symbol)]
  [plusC   (l : ExprC) (r : ExprC)]
  [multC   (l : ExprC) (r : ExprC)]
  [lamC    (arg : symbol) (body : ExprC)]
  [appC    (fun : ExprC) (arg : ExprC)]
  [ifC     (cond : ExprC) (y : ExprC) (n : ExprC)]
  [consC   (car : ExprC) (cdr : ExprC)]; Creates cell with a pair
  [carC    (pair : ExprC)]; Gets 1st element of a pair
  [cdrC    (pair : ExprC)]; Gets 2nd element of a pair
  ; Adicionadas:
  [letC (name : symbol) (arg : ExprC) (body : ExprC)]
  [let*C (args : (listof symbol)) (funcs : (listof ExprC)) (exp : ExprC)]
  [seqC (body : (listof ExprC))]
  [setC (s : symbol) (val : ExprC)]
  [quoteC (s : symbol)]
;  [read-loopC]
  )
#| agora a linguagem aumentada pelo açúcar sintático
 | neste caso a operação de subtração e menus unário
 |#

(define-type ExprS
  [numS    (n : number)]
  [idS     (s : symbol)]
  [lamS    (arg : symbol) (body : ExprS)]
  [appS    (fun : ExprS) (arg : ExprS)]
  [plusS   (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [multS   (l : ExprS) (r : ExprS)]
  [ifS     (c : ExprS) (y : ExprS) (n : ExprS)]
  [consS   (car : ExprS) (cdr : ExprS)]
  [carS    (pair : ExprS)]
  [cdrS    (pair : ExprS)]
  ; Adicionadas:
  [letS    (name : symbol) (arg : ExprS) (body : ExprS)]
  [let*S   (args : (listof symbol)) (funcs : (listof ExprS)) (exp : ExprS)]
  [seqS    (body : (listof ExprS))]
  [setS    (s : symbol) (val : ExprS)]
  [letrecS (arg : symbol) (func : ExprS) (exp : ExprS)]
  [quoteS  (s : symbol)]
 ; [read-loopS]
  )


(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS    (n)        (numC n)]
    [idS     (s)        (idC s)]
    [lamS    (a b)      (lamC a (desugar b))]
    [appS    (fun arg)  (appC (desugar fun) (desugar arg))]
    [plusS   (l r)      (plusC (desugar l) (desugar r))]
    [multS   (l r)      (multC (desugar l) (desugar r))]
    [bminusS (l r)      (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS (e)        (multC (numC -1) (desugar e))]
    [ifS     (c y n)    (ifC (desugar c) (desugar y) (desugar n))]
    [consS   (b1 b2)    (consC (desugar b1) (desugar b2))]
    [carS    (c)        (carC (desugar c))]
    [cdrS    (c)        (cdrC (desugar c))]
    ; Adicionadas:
    [letS (name arg body) (letC name (desugar arg) (desugar body))]
    [let*S (args funcs exp) (let*C args (list (desugar (first funcs)) (desugar (second funcs))) (desugar exp))]
    [seqS (body) (seqC (cons (desugar (first body)) (cond [(not (empty? (rest body))) (cons (desugar (second body)) empty)] [else empty])))]
    [setS (sym val) (setC sym (desugar val))]
    [letrecS (arg fun exp) (letC arg (quoteC '_) (seqC (cons (setC arg (desugar fun)) (cons (desugar exp) empty))))]
    [quoteS (s) (quoteC s)]
   ; [read-loopS () (read-loopC)]

    ))



; We need a new value for the box
(define-type Value
  [numV  (n : number)]
  [closV (arg : symbol) (body : ExprC) (env : Env)]
  [consV (car : Value) (cdr : Value)]
  ; Valor adicional para o quote
  [symV (s : symbol)]
 
  )


; Bindings associate symbol with Boxes
; we need this to be able to change the value of a binding, which is important
; to implement letrec.

(define-type Binding
        [bind (name : symbol) (val : (boxof Value))])


; Env remains the same, we only change the Binding
(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)


; Storage's operations are similar to Env's
;   bind <-> cell
;   mt-env <-> mt-store
;   extend-env <-> override-store


; lookup changes its return type
(define (lookup [varName : symbol] [env : Env]) : (boxof Value); lookup returns the box, we need this to change the value later
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string varName) " não foi encontrado"))] ; livre (não definida)
            [else (cond
                    [(symbol=? varName (bind-name (first env)))   ; achou!
                     (bind-val (first env))]
                    [else (lookup varName (rest env))])]))        ; vê no resto



; Primitive operators
(define (num+ [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (+ (numV-n l) (numV-n r)))]
        [else
             (error 'num+ "Um dos argumentos não é número")]))

(define (num* [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (* (numV-n l) (numV-n r)))]
        [else
             (error 'num* "Um dos argumentos não é número")]))

; Return type for the interpreter, Value


(define (interp [a : ExprC] [env : Env] ) : Value
  (type-case ExprC a
    [numC (n) (numV n) ]
    [idC (n)  (unbox (lookup n env))]; we need to unbox the value in the environment before using it
    [lamC (a b) (closV a b env) ]

 
    ; application of function
    [appC (f a)
          (let ((closure (interp f env))
                (argvalue (interp a env)))
            (type-case Value closure
              [closV (parameter body env)
                     (interp body (extend-env (bind parameter (box argvalue)) env))]
              [else (error 'interp "operation app aplied to non-closure")]
              ))]
   
    ;I left plusC without error-checking
    [plusC (l r)
             (let ((left (interp l env))
                   (right (interp r env)))
               (num+ left right))]
    ;multC
    [multC (l r)
           (let ( (left (interp l env))
                  (right (interp r env)))
             ;in this case type cheking is a little different
             (if (numV? left)
                 (if (numV? right)
                     (num* left right)
                     (error 'interp "second argument of multiplication not a number value"))
                 (error 'interp "first argument of multiplication not a number value"))
                 )]
    ; ifC serializes
    [ifC (c s n) (type-case Value (interp c env)
                   [numV (value)
                        (if (zero? value)
                            (interp n env )
                            (interp s env ))]
                   [else (error 'interp "condition not a number")]
                   )]

    ; Working with lists
    [consC (b1 b2) (let ( (car (interp b1 env))
                          (cdr (interp b2 env)))
                     (consV car cdr))]
    [carC (c) (type-case Value (interp c env)
                [consV (car cdr)
                       car]
                [else (error 'interp "car applied to non-cell")]
                )]
    [cdrC (c) (type-case Value (interp c env)
                [consV (car cdr)
                       cdr]
                [else (error 'interp "cdr applied to non-cell")]
                )]
    ; Adicionadas:
    [letC (name arg body)
          (let* ([new-bind (bind name (box (interp arg env)))] [new-env (extend-env new-bind env)]) (interp body new-env))]
    [let*C (args funcs exp)
           (local ([define first-env (extend-env (bind (first args) (box (interp (first funcs) env))) env)])
             (local ([define second-env (extend-env (bind (second args) (box (interp (second funcs) first-env))) first-env)])
               (interp exp second-env)))]
    [setC (sym val) (local ([define current (lookup sym env)]) (begin (set-box! current (interp val env)) (unbox current)))]
    [seqC (body) (if (empty? (rest body)) (interp (first body) env) (begin (interp (first body) env) (interp (second body) env)))]
    [quoteC (s) (symV s)]
;    [read-loopC ()
 ;               (lambda ()
  ;                (let ((input (read)))
   ;                 (if (and (s-exp->symbol? input) (eq? (s-exp->symbol input) '@end)))
    ;                (begin
     ;                  (display "FINISHED-INTERPRETER")
      ;                 (display "\n")
       ;                (numV 0))
        ;            (begin (display "\ninterpret-command:")
         ;                  (display input)
          ;                 (display "\n")
           ;                (display (interp (desugar (parse input)) mt-env)))
            ;               (display "\n")
             ;              (read-loopC)))]
    ))


; Parser with funny instructions for boxes
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))] ; pode ser um símbolo livre nas definições de função
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (case (s-exp->symbol (first sl))
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (bminusS (parse (second sl)) (parse (third sl)))]
         [(~) (uminusS (parse (second sl)))]
         [(lambda) (lamS (s-exp->symbol (second sl)) (parse (third sl)))] ; definição
         [(call) (appS (parse (second sl)) (parse (third sl)))]
         [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(cons) (consS (parse (second sl)) (parse (third sl)))]
         [(car) (carS (parse (second sl)))]
         [(cdr) (cdrS (parse (second sl)))]
         ;Adicionadas:
         [(let) (letS (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl)))))) (parse (second (s-exp->list (first (s-exp->list (second sl)))))) (parse (third sl)))]
         [(let*) (let*S (list (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl)))))) (s-exp->symbol (first (s-exp->list (second (s-exp->list (second sl)))))))
                        (list (parse (second (s-exp->list (first (s-exp->list (second sl)))))) (parse (second (s-exp->list (second (s-exp->list (second sl)))))))
                              (parse (third sl)))]
         [(seq) (seqS (cons (parse (second sl)) (cond
                                                  [(not (empty? (rest (rest sl)))) (cons (parse (list->s-exp (cons (symbol->s-exp 'seq) (rest (rest sl))))) empty)]
                                                  [else empty])))]
         [(set) (setS (s-exp->symbol (second sl)) (parse (third sl)))]
         [(letrec) (letrecS (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl)))))) (parse (second (s-exp->list (first (s-exp->list (second sl)))))) (parse (third sl)))]
         [(quote) (quoteS (s-exp->symbol (second sl)))]
        ; [(read-loop) (read-loopS)]
         [else (error 'parse "invalid list input")]))]
    [else (error 'parse "invalid input")]))


; Facilitator
(define (interpS [s : s-expression]) (interp (desugar (parse s)) mt-env))

; Examples
(interpS '(+ 10 (call (lambda x (car x)) (cons 15 16))))

(interpS '(call (lambda x (+ x 5)) 8))


(interpS '(call (lambda f (call f (~ 32))) (lambda x (- 200 x))))


; Tests
(test (interp (carC (consC (numC 10) (numC 20)))
              mt-env)
      (numV 10))

(interpS '(quote alan))

; Testes disponibilizados no Telegram:


(test (interpS '(let ((x 100)) x)) (numV 100))

(test (interpS '(let ((x 100)) (+ 1 x))) (numV 101))

(test (interpS '(let ((x 100)) (let ((y (+ x 1))) (+ x y)))) (numV 201))

(test (interpS '(let ((f (lambda x x))) (call f 10))) (numV 10))

(test (interpS '(let ((plus (lambda x (lambda y (+ x y)))))
    (call (call plus 10) 20) )) (numV 30))

(test (interpS '(let* ((x 100) (y (+ x 1))) (+ x y))) (numV 201))

(test (interpS 
    '(let* ((inc (lambda n (+ n 1))) (inc2 (lambda n (call inc (call inc n))))) (call inc2 10)))
    (numV 12))


(test (interpS '(letrec ((f (lambda n (if n (* 2 (call f (- n 1))) 1)))) (call f 10))) (numV 1024))

(test (interpS '(letrec ((f (lambda n (if n (* 2 (call f (- n 1))) 1)))) 10)) (numV 10))

(test (interpS '(letrec ((f (lambda n n))) (call f 7))) (numV 7))


