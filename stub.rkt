#lang plai
(print-only-errors #t)

(define-type Expr
  [num (n number?)]
  [id (v symbol?)]
  [bool (b boolean?)]
  [bin-num-op (op procedure?) (lhs Expr?) (rhs Expr?)]
  [iszero (e Expr?)]
  [bif (test Expr?) (then Expr?) (else Expr?)]
  [with (bound-id symbol?) (bound-body Expr?) (body Expr?)]
  [rec-with (bound-id symbol?) (bound-body Expr?) (body Expr?)]
  [fun (arg-id symbol?) (body Expr?)]
  [app (fun-expr Expr?) (arg-expr Expr?)]
  [tempty]
  [tcons (first Expr?) (rest Expr?)]
  [tfirst (e Expr?)]
  [trest (e Expr?)]
  [istempty (e Expr?)])

(define-type Type
  [t-num]
  [t-bool]
  [t-list (elem Type?)]
  [t-fun (arg Type?) (result Type?)]
  [t-var (v symbol?)]) ; TODO: figure out why this is new in this assignment

(define-type Constraint
  [eqc (lhs Type?) (rhs Type?)])

;------------------------------------------------------------------------------
; main functions
;------------------------------------------------------------------------------

; generate-constraints : symbol Expr -> (listof Constraint)
; TODO: document this
(define (generate-constraints e-id e)
  (type-case Expr e
    [num (n) (list (eqc (t-var e-id) (t-num)))]
    [id (v) (list (eqc (t-var e-id) (t-var v)))]
    ; ...
    [bin-num-op (op lhs rhs)
                (local ([define lhs-id (gensym 'lhs)]
                        [define rhs-id (gensym 'rhs)]
                        [define lhs-c (generate-constraints lhs-id lhs)]
                        [define rhs-c (generate-constraints rhs-id rhs)])
                  (append
                    (list (eqc (t-var e-id) (t-num))
                          (eqc (t-var lhs-id) (t-num))
                          (eqc (t-var rhs-id) (t-num)))
                    lhs-c
                    rhs-c))]
    [else
      (error "Constraint generation is not fully implemented yet.")]))

;------------------------------------------------------------------------------
; auxillary functions
;------------------------------------------------------------------------------

; type=?/mapping : hash hash Type Type -> Bool
; determines if types are equal modulo renaming
(define (type=?/mapping ht1 ht2 t1 t2)
  (define (teq? t1 t2)
    (type=?/mapping ht1 ht2 t1 t2))
  (cond
    [(and (t-num? t1) (t-num? t2)) true]
    [(and (t-bool? t1) (t-bool? t2)) true]
    [(and (t-list? t1) (t-list? t2))
     (teq? (t-list-elem t1) (t-list-elem t2))]
    [(and (t-fun? t1) (t-fun? t2))
     (and (teq? (t-fun-arg t1) (t-fun-arg t2))
          (teq? (t-fun-result t1) (t-fun-result t2)))]
    [(and (t-var? t1) (t-var? t2))
     (local ([define v1 ; the symbol that ht1 says that t1 maps to
               (hash-ref
                 ht1 (t-var-v t1)
                 (lambda ()
                   ; if t1 doesn't map to anything, it's the first
                   ; time we're seeing it, so map it to t2
                   (hash-set! ht1 (t-var-v t1) (t-var-v t2))
                   (t-var-v t2)))]
             [define v2
               (hash-ref
                 ht2 (t-var-v t2)
                 (lambda ()
                   (hash-set! ht2 (t-var-v t2) (t-var-v t1))
                   (t-var-v t1)))])
       ; we have to check both mappings, so that distinct variables
       ; are kept distinct. i.e. a -> b should not be isomorphic to
       ; c -> c under the one-way mapping a => c, b => c.
       (and (symbol=? (t-var-v t2) v1)
            (symbol=? (t-var-v t1) v2)))]
    [(and (Type? t1) (Type? t2)) false]
    [else (error 'type=? "either ~a or ~a is not a Type" t1 t2)]))

; type=? Type -> Type -> Bool
; signals an error if arguments are not variants of Type
(define ((type=? t1) t2)
  (or (type=?/mapping (make-hash) (make-hash) t1 t2)
      ; Unfortunately, test/pred simply prints false;
      ; this helps us see what t2 was.
      (error 'type=?
             "~s and ~a are not equal (modulo renaming)"
             t1 t2)))

; constraint-list=? : Constraint list -> Constraint list -> Bool
; signals an error if arguments are not variants of Constraint
(define ((constraint-list=? lc1) lc2)
  (define htlc1 (make-hash))
  (define htlc2 (make-hash))
  (or (andmap (lambda (c1 c2)
                (and
                  (type=?/mapping
                    htlc1 htlc2
                    (eqc-lhs c1) (eqc-lhs c2))
                  (type=?/mapping
                    htlc1 htlc2
                    (eqc-rhs c1) (eqc-rhs c2))))
              lc1 lc2)
      (error 'constraint-list=?
             "~s and ~a are not equal (modulo renaming)"
             lc1 lc2)))

; parse : s-expression -> Expr
; Converts the given s-expression into a Expr
;   by parsing it according to this grammar:
;   expr ::=       num
;          |       true
;          |       false
;          |       (+ expr expr)
;          |       (- expr expr)
;          |       (* expr expr)
;          |       (iszero expr)
;          |       (bif expr expr expr)
;          |       id
;          |       (with (id expr) expr)
;          |       (rec (id expr) expr)
;          |       (fun (id) expr)
;          |       (expr expr)
;          |       tempty
;          |       (tcons expr expr)
;          |       (tempty? expr)
;          |       (tfirst expr)
;          |       (trest expr)
; where num is a Racket number and id is an identifier not otherwise mentioned in the grammar.
(define (parse s-exp)
  (match s-exp

    ; |   num
    [(? number? s-exp)
      (num s-exp)]

    ; |   true
    ['true
      (bool true)]

    ; |   false
    ['false
      (bool false)]

    ; |   (+ expr expr)
    [(list '+ lhs rhs)
      (bin-num-op +
                  (parse lhs)
                  (parse rhs))]

    ; |   (- expr expr)
    [(list '- lhs rhs)
      (bin-num-op -
                  (parse lhs)
                  (parse rhs))]

    ; |   (* expr expr)
    [(list '* lhs rhs)
      (bin-num-op *
                  (parse lhs)
                  (parse rhs))]

    ; |   (iszero expr)
    [(list 'iszero expr)
      (iszero (parse expr))]

    ; |   (bif expr expr expr)
    [(list 'bif pred true-branch false-branch)
      (bif (parse pred)
           (parse true-branch)
           (parse false-branch))]

    ; |   (with (id expr) expr)
    [(list 'with (list bound-id bound-expr) body)
      (unless (symbol? bound-id)
        (error 'parse "Syntax Error: Non-symbol bind target"))
      (with bound-id
            (parse bound-expr)
            (parse body))]

    ; |   (rec (id expr) expr)
    [(list 'rec (list bound-id bound-expr) body)
      (unless (symbol? bound-id)
        (error 'parse "Syntax Error: Non-symbol bind target"))
      (rec-with bound-id
                (parse bound-expr)
                (parse body))]

    ; |   (fun (id) expr)
    [(list 'fun (list param-id) body)
      (fun param-id
           (parse body))]

    ; |   tempty
    ['tempty
      (tempty)]

    ; |   (tcons expr expr)
    [(list 'tcons fst rst)
      (tcons (parse fst)
             (parse rst))]

    ; |   (tempty? expr)
    [(list 'tempty? expr)
      (istempty (parse expr))]

    ; |   (tfirst expr)
    [(list 'tfirst expr)
      (tfirst (parse expr))]

    ; |   (trest expr)
    [(list 'trest expr)
      (trest (parse expr))]

    ; |   id
    ; NOTE: order matters here;
    ;   if this is earlier we might accidentally catch reserved constants (i.e., tempty, true, and false)
    [(? symbol? s-exp)
      (id s-exp)]

    ; |   (expr expr)
    ; NOTE: order matters here;
    ;   if this is earlier we might accidentally catch 2-length constructs (i.e., tempty?, tfirst, and trest)
    [(list fun-expr arg-expr)
      (app (parse fun-expr)
           (parse arg-expr))]

    [_
      (error 'parse "Syntax error: Does not parse to a valid Expr")]))

  ; tests
    (test (parse '1) (num 1))
    (test (parse 'true) (bool true))
    (test (parse 'false) (bool false))
    (test (parse '{+ 1 2}) (bin-num-op + (num 1) (num 2)))
    (test (parse '{+ 1 {+ 2 3}}) (bin-num-op + (num 1) (bin-num-op + (num 2) (num 3))))
    (test (parse '{- 1 2}) (bin-num-op - (num 1) (num 2)))
    (test (parse '{- 1 {- 2 3}}) (bin-num-op - (num 1) (bin-num-op - (num 2) (num 3))))
    (test (parse '{* 1 2}) (bin-num-op * (num 1) (num 2)))
    (test (parse '{* 1 {* 2 3}}) (bin-num-op * (num 1) (bin-num-op * (num 2) (num 3))))
    (test (parse '{iszero 0}) (iszero (num 0)))
    (test (parse '{iszero {+ 1 2}}) (iszero (bin-num-op + (num 1) (num 2))))
    (test (parse '{bif true 10 20}) (bif (bool true) (num 10) (num 20)))
    (test (parse '{bif (iszero 10) {+ 1 2} {- 1 2}}) (bif (iszero (num 10)) (bin-num-op + (num 1) (num 2)) (bin-num-op - (num 1) (num 2))))
    (test (parse 'x) (id 'x))
    (test (parse '{with {x 2} x}) (with 'x (num 2) (id 'x)))
    (test (parse '{with {x {+ 1 2}} {+ x 3}}) (with 'x (bin-num-op + (num 1) (num 2)) (bin-num-op + (id 'x) (num 3))))
    (test (parse '{with {x {with {x 1} {+ x 2}}} {with {y 3} {+ x y}}})
          (with 'x (with 'x (num 1) (bin-num-op + (id 'x) (num 2))) (with 'y (num 3) (bin-num-op + (id 'x) (id 'y)))))
    (test (parse '{fun {x} x})
          (fun 'x (id 'x)))
    (test (parse '{fun {x} {iszero x}})
          (fun 'x (iszero (id 'x))))
    (test (parse '{f 0}) (app (id 'f) (num 0)))
    (test (parse '{{f 0} {g 1}}) (app (app (id 'f) (num 0)) (app (id 'g) (num 1))))
    (test (parse '{fun {f} {fun {y} {f {+ y 1}}}})
          (fun 'f (fun 'y (app (id 'f) (bin-num-op + (id 'y) (num 1))))))
    (test (parse 'tempty) (tempty))
    (test (parse '{tcons 1 tempty}) (tcons (num 1) (tempty)))
    (test (parse '{tcons {tcons 1 tempty} {tcons 2 {tcons 3 tempty}}}) (tcons (tcons (num 1) (tempty)) (tcons (num 2) (tcons (num 3) (tempty)))))
    (test (parse '{tempty? tempty}) (istempty (tempty)))
    (test (parse '{tempty? (tcons 1 tempty)}) (istempty (tcons (num 1) (tempty))))
    (test (parse '{tfirst tempty}) (tfirst (tempty)))
    (test (parse '{tfirst (tcons 1 tempty)}) (tfirst (tcons (num 1) (tempty))))
    (test (parse '{trest tempty}) (trest (tempty)))
    (test (parse '{trest (tcons 1 tempty)}) (trest (tcons (num 1) (tempty))))

;------------------------------------------------------------------------------
; tests
;------------------------------------------------------------------------------

(define num-test-exp (num 1))
(define num-test-constraints
  (list (eqc (t-var 'top) (t-num))))
(test/pred (generate-constraints (gensym 'top) num-test-exp)
           (constraint-list=? num-test-constraints))

(define plus-test-expr (bin-num-op + (num 1) (num 2)))
(define plus-test-constraints
  (list (eqc (t-var 'top) (t-num))
        (eqc (t-var 'binop-left) (t-num))
        (eqc (t-var 'binop-right) (t-num))
        (eqc (t-var 'binop-left) (t-num))
        (eqc (t-var 'binop-right) (t-num))))
(test/pred (generate-constraints (gensym 'top) plus-test-expr)
           (constraint-list=? plus-test-constraints))

