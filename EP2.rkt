#lang plai-typed

#|
 | EP#02 - MAC0316 - Conceitos Fundamentais de Linguagens de Programação
 | Professor:   Alan Mitchell Durham
 | Aluno:       Francisco Membrive
 | Data:        06/11/2024
 | Objetivo:    Incrementar o interpretador disponibilizado com as funções
 |              solicitadas no enunciado. 
 |              A versão do EP1 utilizada foi a disponibilizada pelo monitor.
 |
 |
 |              
 |              
 |              
 |#

(define-type ExprC
  [numC    (n : number)]
  [idC     (s : symbol)]
  [plusC   (l : ExprC) (r : ExprC)]
  [multC   (l : ExprC) (r : ExprC)]
  [lamC    (arg : symbol) (body : ExprC)]
  [appC    (fun : ExprC) (arg : ExprC)]
  [ifC     (cond : ExprC) (y : ExprC) (n : ExprC)]
  [consC   (car : ExprC) (cdr : ExprC)]
  [carC    (pair : ExprC)]
  [cdrC    (pair : ExprC)]
  [letrecC (s : symbol) (v : ExprC) (r : ExprC)]
  [quoteC  (s : symbol)]
  [seqC    (e1 : ExprC) (e2 : ExprC)]
  [equal?C (l : ExprC) (r : ExprC)]
  )


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
  [letS    (name : symbol)  (value : ExprS) (body : ExprS)]
  [let*S   (name1 : symbol) (value1 : ExprS) (name2 : symbol) (value2 : ExprS) (body : ExprS)]
  [letrecS (name : symbol)  (value : ExprS) (body : ExprS)]
  [quoteS  (name : symbol)]
  [seqS    (e1 : ExprS) (e2 : ExprS)]
  [equal?S  (l : ExprS) (r : ExprS)]
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
    [seqS    (l r)      (seqC (desugar l) (desugar r))]
    [letS    (name value body)
     (appC (lamC name (desugar body)) (desugar value))]
    [let*S   (name1 value1 name2 value2 body)
     (appC (lamC name1 (appC (lamC name2 (desugar body)) (desugar value2))) (desugar value1))]
    [letrecS (name value body)    (letrecC name (desugar value) (desugar body))]
    [quoteS  (name)        (quoteC name)]
    [equal?S (l r) (equal?C (desugar l) (desugar r))]
    ))


(define-type-alias Promise (boxof Value))

(define-type Value
  [numV  (n : number)]
  [closV (arg : symbol) (body : ExprC) (env : Env)]
  [consV (car : Promise) (cdr : Promise)]
  [symV  (s : symbol)]
  [suspV (body : ExprC) (env : Env)]
  )


(define-type Binding [bind (name : symbol) (val : Promise)])
(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)


(define (lookup [varName : symbol] [env : Env]) : Promise
  (cond
    [(empty? env) (error 'lookup (string-append (symbol->string varName) " não foi encontrado"))]
    [else (if (symbol=? varName (bind-name (first env)))
              (bind-val (first env))
              (lookup varName (rest env)))]))

(define (query-promise [promise : Promise]) : Value
  (type-case Value (unbox promise)
    [suspV (body susp-env)
      (let* ([finalValue (interp body susp-env)])
        (begin (set-box! promise finalValue)
               finalValue))]
    [else (unbox promise)]))

(define (force [v : Value]) : Value
  (if (suspV? v)
      (query-promise (box v))
      v))

(define (num+ [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r)) (numV (+ (numV-n l) (numV-n r)))]
    [else (error 'num+ "Um dos argumentos não é número")]))

(define (num* [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r)) (numV (* (numV-n l) (numV-n r)))]
    [else (error 'num* "Um dos argumentos não é número")]))

(define (interp [a : ExprC] [env : Env]) : Value
  (type-case ExprC a
    [numC (n) (numV n)]
    [idC (n)
      (let ([promise (lookup n env)])
        (query-promise promise))]
    [lamC (a b) (closV a b env)]
    [appC (f a)
      (let* ([func (interp f env)])
        (type-case Value func
          [closV (arg body f-env)
            (let* ([promise (box (suspV a env))]
                   [new-env (extend-env (bind arg promise) f-env)])
              (interp body new-env))]
          [else (error 'appC "Esperava uma função")]))]
    [plusC (l r)
      (let* ([v-l (force (interp l env))]
             [v-r (force (interp r env))])
        (num+ v-l v-r))]
    [multC (l r)
      (let* ([v-l (force (interp l env))]
             [v-r (force (interp r env))])
        (num* v-l v-r))]
    [ifC (cond y n)
      (let* ([v-cond (force (interp cond env))])
        (if (zero? (numV-n v-cond))
            (interp n env)
            (interp y env)))]
    [consC (car cdr)
      (let* ([promise-car (box (suspV car env))]
             [promise-cdr (box (suspV cdr env))])
        (consV promise-car promise-cdr))]
    [carC (pair)
      (let* ([v-pair (force (interp pair env))])
        (type-case Value v-pair
          [consV (car cdr)
            (query-promise car)]
          [else (error 'car "erro em car")]))]
    [cdrC (pair)
      (let* ([v-pair (force (interp pair env))])
        (type-case Value v-pair
          [consV (car cdr)
            (query-promise cdr)]
          [else (error 'cdr "erro em cdr")]))]
    [letrecC (name val body)
             (let* ([promise (box (suspV val mt-env))] 
                    [new-env (extend-env (bind name promise) env)]
                    [_ (set-box! promise (suspV val new-env))] 
                    [result (interp body new-env)])
               result)]

    [quoteC (s) (symV s)]
    [seqC (e1 e2)
      (begin (interp e1 env)
             (interp e2 env))]
    [equal?C (l r)
      (let* ([v1 (force (interp l env))]
             [v2 (force (interp r env))])
        (if (equal? v1 v2)
            (numV 1)
            (numV 0)))]
    ))

(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (case (s-exp->symbol (first sl))
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (bminusS (parse (second sl)) (parse (third sl)))]
         [(~) (uminusS (parse (second sl)))]
         [(lambda) (lamS (s-exp->symbol (second sl)) (parse (third sl)))]
         [(call) (appS (parse (second sl)) (parse (third sl)))]
         [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(cons) (consS (parse (second sl)) (parse (third sl)))]
         [(car) (carS (parse (second sl)))]
         [(cdr) (cdrS (parse (second sl)))]
         [(let)
          (let ([terms (s-exp->list (first (s-exp->list (second sl))))])
            (letS (s-exp->symbol (first terms))
                  (parse (second terms))
                  (parse (third sl))))]
         [(let*)
          (let ([first-term (s-exp->list (first (s-exp->list (second sl))))]
                [second-term (s-exp->list (second (s-exp->list (second sl))))])
            (let*S (s-exp->symbol (first first-term))
                   (parse (second first-term))
                   (s-exp->symbol (first second-term))
                   (parse (second second-term))
                   (parse (third sl))))]
         [(letrec)
          (let ([terms (s-exp->list (first (s-exp->list (second sl))))])
            (letrecS (s-exp->symbol (first terms))
                      (parse (second terms))
                      (parse (third sl))))]
         [(quote) (quoteS (s-exp->symbol (second sl)))]
         [(equal?) (equal?S (parse (second sl)) (parse (third sl)))]
         [else (error 'parse
                      (string-append
                       "invalid list input: unrecognized expression start: "
                       (symbol->string (s-exp->symbol (first sl)))))]))]
    [else (error 'parse "invalid input: unknown s-expression type")]))

(define (interpS [s : s-expression]) : Value
  (interp (desugar (parse s)) mt-env))

; Testes disponibilizados no Telegram:

(test (interpS '(letrec ((halt (lambda x (call halt x))))
                  (let ((death (call halt 0))) 1))) 
      (numV 1))

(test (interpS '(letrec ((halt (lambda x (call halt x))))
                  (car (cons 2 (call halt 0))))) 
      (numV 2))

(test (interpS '(letrec ((halt (lambda x (call halt x))))
                  (cdr (cons (call halt 0) 3)))) 
      (numV 3))

(test (interpS '(letrec ((halt (lambda x (call halt x))))
                  (let ((first (lambda x (lambda y x))))
                    (call (call first 4) (call halt 0))))) 
      (numV 4))

(test (interpS '(letrec ((halt (lambda x (call halt x))))
                  (let ((second (lambda x (lambda y y))))
                    (call (call second (call halt 0)) 5)))) 
      (numV 5))

(test (interpS '(letrec ((iterate (lambda f (lambda x (cons x (call (call iterate f) (call f x)))))))
                 (let ((things (call (call iterate (lambda x (* 10 x))) 1)))

                   (+ (+ (car things) (car (cdr things)))
                      (car (cdr (cdr things)))))

                 )) 
      (numV 111))

(test (interpS '(letrec ((drop (lambda n (lambda xs (if n (call (call drop (- n 1)) (cdr xs)) xs)))))
                  (letrec ((iterate (lambda f (lambda x (cons x (call (call iterate f) (call f x)))))))
                    (let ((things (call (call drop 3) (call (call iterate (lambda x (* 10 x))) 1))))

                      (+ (+ (car things) (car (cdr things)))
                         (car (cdr (cdr things)))))
                    
                    ))) 
      (numV 111000))
