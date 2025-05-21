#lang plai-typed

#|
 | EP#03 - MAC0316 - Conceitos Fundamentais de Linguagens de Programação
 | Professor:   Alan Mitchell Durham
 | Aluno:       Francisco Membrive
 | Data:        16/12/2024
 | Objetivo:    Incrementar o interpretador disponibilizado com as funções
 |              solicitadas no enunciado. 
 |              Os comentários originais foram mantidos.
 |
 |
 |              
 |              
 |              
 |#

#| primeiro as expressões "primitivas", ou seja, diretamente interpretadas
 |#

(define-type ExprC
  [numC    (n : number)]
  [idC     (s : symbol)]
  [plusC   (l : ExprC) (r : ExprC)]
  [multC   (l : ExprC) (r : ExprC)]
  [ifC     (cond : ExprC) (y : ExprC) (n : ExprC)]
  [letC (var : symbol) (expression : ExprC) (body : ExprC)]
  [quoteC  (sym : symbol)]
  [readloopC (placeholder : symbol)]
  [nullC]
  [seqC  (statement1 : ExprC) (statement2 : ExprC)]
  [setC  (varName : symbol) (statement : ExprC)]
  
;Novo:
  
  [classC  (superClass : symbol) (instVar : symbol) (method1 : ExprC) (method2 : ExprC)]
  [regularMethodC (name : symbol) (arg : symbol) (body : ExprC)]
  [primitiveMethodC (name : symbol) (primNumber : number)]
  [newC (class : symbol) (value : ExprC)]
  [sendC (receiver : ExprC) (method : symbol) (arg : ExprC)]

  )
#| agora a linguagem aumentada pelo açúcar sintático
 | neste caso a operação de subtração e menus unário
 |#

(define-type ExprS
  [numS    (n : number)]
  [idS     (s : symbol)]
  [plusS   (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [multS   (l : ExprS) (r : ExprS)]
  [ifS     (c : ExprS) (y : ExprS) (n : ExprS)]
  [letS    (var : symbol) (exp : ExprS) (body : ExprS)]
  [quoteS  (sym : symbol)]
  [readloopS (placeholder : symbol)]
  [seqS (statement1 : ExprS) (statement2 : ExprS)]
  [setS (variable : symbol) (statement : ExprS)]
  ;Deixei as opções aqui, para facilitar, basta retirar o ";" 
  [newS    (class : symbol) (value : ExprS)]
  [classS  (superClass : symbol) (instVar : symbol) (method1 : ExprS ) (method2 : ExprS)]
  [regularMethodS (name : symbol) (arg : symbol) (body : ExprS)]
  [primitiveMethodS (name : symbol) (primNumber : number)]
  [sendS   (receiver : ExprS) (method : symbol) (arg : ExprS)]
  [nullS  ]
  )


(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS    (n)        (numC n)]
    [idS     (s)        (idC s)]
    [plusS   (l r)      (plusC (desugar l) (desugar r))]
    [multS   (l r)      (multC (desugar l) (desugar r))]
    [bminusS (l r)      (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS (e)        (multC (numC -1) (desugar e))]
    [ifS     (c y n)    (ifC (desugar c) (desugar y) (desugar n))]
    [letS    (v e b)    (letC v (desugar e) (desugar b))]
    [quoteS  (sym) (quoteC sym)]
    [readloopS (s) (readloopC s)]
    [nullS  ()  (nullC)]
    [seqS (st1 st2) (seqC (desugar st1) (desugar st2))]
    [setS (var st)  (setC var (desugar st))]
    ; adicionado:
    
    [classS  (superClass instVar method1 method2) (classC superClass instVar (desugar method1) (desugar method2))]
    [regularMethodS (name arg body) (regularMethodC name arg (desugar body))]
    [primitiveMethodS (name primNumber) (primitiveMethodC name primNumber)]
    [newS (class value) (newC class (desugar value))]
    [sendS (receiver method arg) (sendC (desugar receiver) method (desugar arg))]
 
    ))

(define-type MethodDefinition
  [regularMethod (par : symbol) (body : ExprC)]
  [primitiveMethod (num : number)])

; We need a new value for the box
(define-type Value
  [numV  (n : number)]
  ;[closV (arg : symbol) (body : ExprC) (env : Env)]
  ;[consV (car : Value) (cdr : Value)]
  [classV (superClass : symbol) (instVar : symbol) (method1 : Value) (method2 : Value)]
  [methodV (name : symbol) (def : MethodDefinition)]
  [symV (sym : symbol)]
  [objectV (Classe : Value) (superClasse : Value) (instVar : Binding)]
  [nullV ]
  )


; Bindings associate symbol with Values
(define-type Binding
        [bind (name : symbol) (val : (boxof Value))])
; Env remains the same, we only change the Binding
(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)

(define (methodLookup [name : symbol] [object : Value]) : Value
  (cond
    [(equal? object (nullV))
     (interp (sendC (idC 'self) 'mensagemDesconhecida (quoteC name))
             (extend-env (bind 'self (box object)) mt-env))]
    [else (cond
            [(symbol=? name (methodV-name (classV-method1 (objectV-Classe object))))
             (classV-method1 (objectV-Classe object))]
            [(symbol=? name (methodV-name (classV-method2 (objectV-Classe object))))
             (classV-method2 (objectV-Classe object))]
            [else (methodLookup name (objectV-superClasse object))])]))

(define classObject
  (classV 'null 'dummy (methodV 'name1 (regularMethod 'method1 (numC 33)))
                       (methodV 'name2 (regularMethod 'method2 (numC 33)))))

(define objectObject
  (objectV classObject (numV 0) (bind 'none (box (numV 33)))))


(define self (lambda (env) objectObject))

(define PrimitiveMethodVector
  (make-vector 2 (lambda ([x : Value]) : Value
                   (error 'primitive "invalid primitive method"))))

(vector-set! PrimitiveMethodVector 1
             (lambda ([methodName : Value])
               (type-case Value methodName
                 [symV (symbolValue)
                       (error 'messaging
                              (string-append "mensagemDesconhecida:"
                                             (symbol->string symbolValue)))]
                 [else (error 'wrongArgument
                              "Wrong Argument: primitive 1 should receive a symV")])))


; auxiary functions for messageLookup                                         
(define (lookup [varName : symbol] [env : Env]) : (boxof Value)
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string varName) " não foi encontrado"))] ; livre (não definida)
            [else (cond
                    [(symbol=? varName (bind-name (first env)))   ; achou!
                     (bind-val (first env))]
                    [else (lookup varName (rest env))])]))        ; vê no resto

(define (objectEnvChain v baseEnv)
  (cond
    [(objectV? v)
     (objectEnvChain (objectV-superClasse v)
                     (extend-env (objectV-instVar v) baseEnv))]
    [else baseEnv]))


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


(define (interp [a : ExprC] [objectEnv : Env]) : Value
  (type-case ExprC a
    [nullC () (nullV)]
    [numC (n) (numV n) ]
    [idC (n)  (unbox (lookup n objectEnv))]; cascading search, first in env then in sto
    ;I left plusC without error-checking
    [plusC (l r)
             (let ((left (interp l objectEnv ))
                   (right (interp r objectEnv )))
               (num+ left right))]
    ;multC
    [multC (l r)
           (let ( (left (interp l objectEnv ))
                  (right (interp r objectEnv )))
             ;in this case type cheking is a little different
             (if (numV? left)
                 (if (numV? right)
                     (num* left right)
                     (error 'interp "second argument of multiplication not a number value"))
                 (error 'interp "first argument of multiplication not a number value"))
                 )]
    ; ifC serializes
    [ifC (c s n) (type-case Value (interp c objectEnv )
                   [numV (value)
                        (if (zero? value)
                            (interp n objectEnv )
                            (interp s objectEnv ))]
                   [else (error 'interp "condition not a number")]
                   )]
    [quoteC  (s) (symV s)]
    [readloopC (ph) (letrec ( (read-till-end (lambda ()
                                              (let ( (input (read)))
                                                (if (and (s-exp-symbol? input )
                                                         (eq? (s-exp->symbol input) '@END))
                                                    (begin (display 'FINISHED-READLOOP)
                                                           (symV  'END_OF_loop))
                                                    (begin (display (interp (desugar (parse input)) objectEnv ))
                                                           (read-till-end)))))))
                     (read-till-end))]
    [letC (variable expression body)
          (let ((value (interp expression objectEnv )))
            (interp body
                    (extend-env (bind variable (box value)) objectEnv)
                    ))]
    [seqC (firstCommand secondCommand)
          (begin (interp firstCommand objectEnv)
                 (interp secondCommand objectEnv))]
    [setC  (variableName statement)
           (let ((varBox (lookup variableName objectEnv))
                 (value (interp statement objectEnv)))
             (begin (set-box! varBox value)
                    value))]
    ;adicionado:
    
    [classC (superClass instVar method1 method2)
            (classV superClass instVar (interp method1 objectEnv) (interp method2 objectEnv))]

    [regularMethodC (name arg body) (methodV name (regularMethod arg body))]

    [primitiveMethodC (name primNumber) (methodV name (primitiveMethod primNumber))]

    [newC (class value)
          (let ([Classe (unbox (lookup class objectEnv))])
            (objectV
             Classe
             (if (equal? (classV-superClass Classe) (classV-superClass classObject))
                 objectObject
                 (interp (newC (classV-superClass Classe) (numC 0)) objectEnv))
             (bind (classV-instVar Classe) (box (interp value objectEnv)))))]

    [sendC (receiver methodName argExpr)
           (let* ([objeto (interp receiver objectEnv)]
                  [methodVal (methodLookup methodName objeto)]
                  [metDef (methodV-def methodVal)])
             (type-case MethodDefinition metDef
               [regularMethod (par bodyExprC)
                              (interp bodyExprC
                                      (extend-env (bind 'self (box objeto))
                                                  (extend-env (bind par (box (interp argExpr objectEnv)))
                                                              (objectEnvChain objeto objectEnv))))]


               [primitiveMethod (primNumber)
                                ((vector-ref PrimitiveMethodVector primNumber)
                                 (interp argExpr objectEnv))]))]

     
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
          [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(quote) (quoteS (s-exp->symbol (second sl)))]
         [(let) (letS (s-exp->symbol (second sl))
                      (parse (third sl))
                      (parse (fourth sl)))]
          [(set!) (setS (s-exp->symbol (second sl))
                      (parse (third sl)))]
         [(seq) (seqS (parse (second sl))
                      (parse (third sl)))]
         ;adicionado:
         [(class) (classS (s-exp->symbol (second sl))
                          (s-exp->symbol (third sl))
                          (parse (fourth sl))
                          (parse (fourth (rest sl))))]

         [(regularMethod) (regularMethodS (s-exp->symbol (second sl))
                                          (s-exp->symbol (third sl))
                                          (parse (fourth sl)))]

         [(new) (newS (s-exp->symbol (second sl))
                      (parse (third sl)))]
         
         [(send) (sendS (parse (second sl))
               (s-exp->symbol (third sl))
               (parse (fourth sl)))]

         
        [else (error 'parse "invalid list input")]
         ))]
    [else (error 'parse "invalid input")]
    ))
 

; Facilitator
; Enviromnent needs to be intialzed with the association for the Object class, which needs to be defined elsewhere 
(define initialObjectEnv (extend-env (bind 'Object (box classObject)) mt-env))
(define (interpS [s : s-expression]) : Value
  (interp (desugar (parse s)) initialObjectEnv ))

; Examples
;(interpS '(class Object i (regularMethod m1 x x) (regularMethod m2 x i)))
;(interpS '(let classe1 (class Object i (regularMethod m1 x x) (regularMethod m2 x i))
;            (let object1 (new classe1 1) (send object1 m1 5))))
;(interpS '(let classe1 (class Object i (regularMethod m1 x x) (regularMethod m2 x i))
;            (let object1 (new classe1 1) (send object1 m2 5))))
; no proximo exemplo definimos um novo m1 em uma subclasse, instanciamos e mandamos a mensagem m2 para no novo
;objeto. O interpretador deve voltar o resultado de m1 da subclasse. (
;(interpS '(let classe1 (class Object i (regularMethod m1 x i) (regularMethod m2 x (send self m1 x)))
;            (let classe2 (class classe1 j (regularMethod m1 x (quote subclassregularMethod)) (regularMethod m3 y y))
;              (let object2 (new classe2 200) (send object2 m2 55)))))
;(interpS '(let classe1 (class Object i (regularMethod m1 x i) (regularMethod m2 x (send self m1 x)))
;            (let classe2 (class classe1 j (regularMethod m1 x (quote subclassregularMethod)) (regularMethod m3 y y))
;              (let object2 (new classe2 200) (send object2 m22 55)))))

; Testes disponibilizados pelo monitor:



(test ; Métodos e variáveis de instância funcionam
  (interpS '(let Classezinha (class Object i
                         (regularMethod beep x x)
                         (regularMethod boop _ i))

            (let objetinho (new Classezinha 1)
              (+ (send objetinho beep 10)
                 (send objetinho boop 0)
                 ))))
  (numV 11))

(test ; Self funciona
  (interpS '(let Classezinha (class Object i 
                          (regularMethod beep x (+ 10 x))
                          (regularMethod boop x (send self beep (+ 1 x))))

              (let objetinho (new Classezinha 0) 
                (send objetinho boop 0))))
  (numV 11))

(test ; Sobrescrita funciona
  (interpS '(let Classezinha1 (class Object i 
                          (regularMethod beep _ 9)
                          (regularMethod boop _ 10))

              (let Classezinha2 (class Classezinha1 j
                            (regularMethod beep _ 1)
                            (regularMethod unused _ 0))

                (let objetinho (new Classezinha2 0) 
                  (+ (send objetinho beep 0)
                     (send objetinho boop 0))))))
  (numV 11))

(test ; Sobrescrita com self funciona
  (interpS '(let Classezinha1 (class Object i 
                          (regularMethod beep x 9)
                          (regularMethod boop x (send self beep x)))

              (let Classezinha2 (class Classezinha1 j
                            (regularMethod beep _ 11)
                            (regularMethod unused _ 0))

                (let objetinho (new Classezinha2 0) 
                  (send objetinho boop 0)))))
  (numV 11))

(test ; Set com variáveis de instância funciona
  (interpS '(let Classezinha1 (class Object
                           i
                           (regularMethod setVariable x (set! i x))
                           (regularMethod getVariable x i))

              (let objetinho (new Classezinha1 9)
                (seq (send objetinho setVariable 11)
                     (send objetinho getVariable 0)))))
  (numV 11))


(test ; Variáveis de instância classes filhas funcionam corretamente
  (interpS '(let Classezinha1 (class Object
                           i
                           (regularMethod getI _ i)
                           (regularMethod beep x x))

              (let Classezinha2 (class Classezinha1
                             j
                             (regularMethod getJ _ j)
                             (regularMethod beep x x))

                (let objetinho (new Classezinha2 11)
                  (send objetinho getJ 0)))))
  (numV 11))

(test ; Acessar de instância de classes ancestrais devolve null
  (interpS '(let Classezinha1 (class Object
                           i
                           (regularMethod getI _ i)
                           (regularMethod beep x x))

              (let Classezinha2 (class Classezinha1
                             j
                             (regularMethod getJ _ j)
                             (regularMethod beep x x))

                (let objetinho (new Classezinha2 9)
                  (send objetinho getI 0)))))
  (nullV))


(test ; É possível acessar e modificar variáveis de instância dos pais
  (interpS '(let Classezinha1 (class Object
                           i
                           (regularMethod getI _ i)
                           (regularMethod setI x (set! i x)))

              (let Classezinha2 (class Classezinha1
                             j
                             (regularMethod getJ _ j)
                             (regularMethod setJ x (set! j x)))

                (let Classezinha3 (class Classezinha2 
                                    k 
                                    (regularMethod getK _ k)
                                    (regularMethod setK x (set! k x))
                                    )

                (let objetinho (new Classezinha3 9)
                  (seq 
                    (send objetinho setI 1)

                    (seq 
                       (send objetinho setJ 10)

                       (seq 
                         (send objetinho setK 100)

                         (+ (send objetinho getI 0)
                            (+ 
                              (send objetinho getJ 0)
                              (send objetinho getK 0)))
                         ))))))))
  (numV 111))

(test ; É possível modificar variáveis de instância dos pais pelos métodos dos filhos
  (interpS '(let Classezinha1 (class Object
                           i
                           (regularMethod getI _ i)
                           (regularMethod unused _ 0))

              (let Classezinha2 (class Classezinha1
                             j
                             (regularMethod setI x (set! i x))
                             (regularMethod getJ _ j))

                (let Classezinha3 (class Classezinha2 
                                    k 
                                    (regularMethod setJ x (set! j x))
                                    (regularMethod unused _ 0))

                (let objetinho (new Classezinha3 9)
                  (seq 
                    (send objetinho setI 1)

                    (seq 
                       (send objetinho setJ 10)

                       (+ 
                         (send objetinho getI 0)
                         (send objetinho getJ 0))
                       )))))))
  (numV 11))

(test ; Objetos são independentes
  (interpS '(let Classezinha1 (class Object
                           i
                           (regularMethod getI _ i)
                           (regularMethod setI x (set! i x)))

              (let Classezinha2 (class Classezinha1
                             j
                             (regularMethod getJ _ j)
                             (regularMethod setJ x (set! j x)))

                (let objetinho1 (new Classezinha2 1)
                  (seq 
                    (send objetinho1 setI 10)

                    (let objetinho2 (new Classezinha2 100) 
                      (seq 
                        (send objetinho2 setI 1000)

                        (+ (send objetinho1 getI 0)
                           (+ 
                             (send objetinho1 getJ 0)
                             (+ (send objetinho2 getI 0)
                                (send objetinho2 getJ 0))))
                        )))))))
  (numV 1111))
