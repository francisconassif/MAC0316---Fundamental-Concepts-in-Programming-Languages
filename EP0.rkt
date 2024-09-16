#lang plai-typed

#|
 | EP#00 - MAC0316 - Conceitos Fundamentais de Linguagens de Programação
 | Professor:   Alan Mitchell Durham
 | Aluno:       Francisco Membrive
 | Data:        16/09/2024
 | Objetivo:    Incrementar o interpretador construído em aula com mais operações.
 |              Em cada seção do código, as operações adicionadas ficaram na sub-
 |              seção "Adicionadas".
 |#

(define-type ArithC
  [numC (n : number)]
  [boolC (b : boolean)]
  [andC (l : ArithC) (r : ArithC)]
  [plusC (l : ArithC) (r : ArithC)]
  [multC (l : ArithC) (r : ArithC)]
  [lessC (l : ArithC) (r : ArithC)]
  [ifC  (c : ArithC)  (t : ArithC) (e : ArithC)]

;; Adicionadas:
  [divC  (l : ArithC) (r : ArithC)]     ; Divisão
  [orC   (l : ArithC) (r : ArithC)]     ; Or
  [equalC   (l : ArithC) (r : ArithC)]  ; Igualdade
  [gtC   (l : ArithC) (r : ArithC)]     ; Maior que
  [notC  (a : ArithC)])                 ; Not


; Incluindo o sinal negativo
(define-type ArithS
  [numS    (n : number)]
  [boolS   (b : boolean)]
  [andS    (l : ArithS) (r : ArithS)]
  [plusS   (l : ArithS) (r : ArithS)]
  [multS   (l : ArithS) (r : ArithS)]
  [bminusS (l : ArithS) (r : ArithS)]
  [lessS   (l : ArithS) (r : ArithS)]
  [ifS  (c : ArithS) (t : ArithS) (e : ArithS)]

;; Adicionadas:
  [divS    (l : ArithS) (r : ArithS)]       ; Divisão
  [orS     (l : ArithS) (r : ArithS)]       ; Or
  [equalS     (l : ArithS) (r : ArithS)]    ; Igualdade
  [gtS     (l : ArithS) (r : ArithS)]       ; Maior que
  [notS    (a : ArithS)]                    ; Not
  [uminusS    (a : ArithS)])                ; Menos unário

; Nova "desugar", ou quase

(define (desugar [as : ArithS]) : ArithC
  (type-case ArithS as
    [numS    (n)   (numC n)]
    [boolS   (b)   (boolC b)]
    [andS    (l r) (andC (desugar l) (desugar r))]
    [plusS   (l r) (plusC (desugar l) (desugar r))]
    [multS   (l r) (multC (desugar l) (desugar r))]
    [lessS  (l r)  (lessC (desugar l) (desugar r))]
    [ifS (c t e) (ifC (desugar c) (desugar t) (desugar e))]

    ;;Adicionadas:
    [divS    (l r) (divC (desugar l) (desugar r))]      ; Divisão
    [orS     (l r) (orC (desugar l) (desugar r))]       ; Or
    [equalS     (l r) (equalC (desugar l) (desugar r))] ; Igualdade
    [notS    (a)   (notC (desugar a))]                  ; Not
    
    ;
    ;Abaixo todos os operadores que são açúcar sintático
    ; 
    [gtS     (l r) (gtC (desugar l) (desugar r))]       ; Maior que
    [uminusS    (a)   (multC (desugar a) (numC -1))]    ; Menos unário
    [bminusS (l r) (plusC (desugar l) (multC (numC -1) (desugar r)))]

    ))


; O interpretador é o mesmo, pois no final ainda temos ArithC
(define (interp [a : ArithC]) : number
  (type-case ArithC a
    [numC   (n) n]
    [boolC  (b) (if b 1 0)]
    [andC  (l r)(if (and (not (=  (interp l) 0)) (not (= (interp r) 0))) 1 0)]
    [plusC  (l r) (+ (interp l) (interp r))]
    [multC  (l r) (* (interp l) (interp r))]
    [lessC  (l r) (if (< (interp l) (interp r)) 1 0)]
    [ifC    (c t e) (if (not (= (interp c) 0))
                        (interp t)
                        (interp e))]
    
    ;; Adicionadas:
    [divC  (l r) (/ (interp l) (interp r))]                         ; Divisão
    [orC    (l r) (if (or (> (interp l) 0) (> (interp r) 0)) 1 0)]  ; Or
    [equalC    (l r) (if (= (interp l) (interp r)) 1 0)]            ; Igualdade
    [gtC    (l r) (if (> (interp l) (interp r)) 1 0)]               ; Maior que
    [notC   (a)   (if (= (interp a) 0) 1 0)] ))                     ; Not


; o parser muda mais um pouco
(define (parse [s : s-expression]) : ArithS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-boolean? s) (boolS (s-exp->boolean s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (case (s-exp->symbol (first sl))
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (bminusS (parse (second sl)) (parse (third sl)))]
         [(and) (andS (parse (second sl)) (parse (third sl)))]
         [(<) (lessS  (parse (second sl)) (parse (third sl)))]
         [(if)(ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]

         ;; Adicionadas:
         [(/) (divS (parse (second sl)) (parse (third sl)))]    ; Divisão
         [(or) (orS (parse (second sl)) (parse (third sl)))]    ; Or
         [(=) (equalS (parse (second sl)) (parse (third sl)))]  ; Igualdade
         [(>) (gtS (parse (second sl)) (parse (third sl)))]     ; Maior que
         [(not) (notS (parse (second sl)))]                     ; Not
         [(~) (uminusS (parse (second sl)))]                    ; Menos unário

         [else (error 'parse "invalid list input")]))]
    [else (error 'parse "invalid input")]))

(define (interpS [ s : ArithS] ) : number
  (interp (desugar s)))
