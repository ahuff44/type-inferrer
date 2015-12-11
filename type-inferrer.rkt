#lang plai
(print-only-errors #t)
(halt-on-errors #t)

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

;------------------------------------------------------------------------------
; main functions
;------------------------------------------------------------------------------

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
    [(list 'with (list bound-id bound-expr) with-body)
      (unless (symbol? bound-id)
        (error 'parse "Syntax Error: Non-symbol bind target"))
      (with bound-id
            (parse bound-expr)
            (parse with-body))]

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

; alpha-vary/helper : hash<symbol, symbol> Expr -> Expr
; TODO: document this
(define (alpha-vary/helper hash expr)
  (define simple-recurse ((curry alpha-vary/helper) hash))
  (type-case Expr expr
    [num (n)
      (num n)]
    [id (v)
      (id (hash-ref hash v (lambda ()
                             (error 'alpha-vary "Type Error: Unbound identifier"))))]
    [bool (b)
      (bool b)]
    [bin-num-op (op lhs rhs)
      (bin-num-op op (simple-recurse lhs) (simple-recurse rhs))]
    [iszero (e)
      (iszero (simple-recurse e))]
    [bif (c t e)
      (bif (simple-recurse c) (simple-recurse t) (simple-recurse e))]
    [with (bound-id bound-body with-body)
      (let* ([new-id (gensym bound-id)]
             [new-hash (hash-set hash bound-id new-id)])
        (with new-id
              (simple-recurse bound-body)
              (alpha-vary/helper new-hash with-body)))]
    [rec-with (bound-id bound-body with-body)
      (let* ([new-id (gensym bound-id)]
             [new-hash (hash-set hash bound-id new-id)])
        (rec-with new-id
                  (alpha-vary/helper new-hash bound-body)
                  (alpha-vary/helper new-hash with-body)))]
    [fun (arg-id body)
      (let* ([new-id (gensym arg-id)]
             [new-hash (hash-set hash arg-id new-id)])
        (fun new-id (alpha-vary/helper new-hash body)))]
    [app (fun-expr arg-expr)
      (app (simple-recurse fun-expr) (simple-recurse arg-expr))]
    [tempty ()
      (tempty)]
    [tcons (fst rst)
      (tcons (simple-recurse fst) (simple-recurse rst))]
    [tfirst (e)
      (tfirst (simple-recurse e))]
    [trest (e)
      (trest (simple-recurse e))]
    [istempty (e)
      (istempty (simple-recurse e))]))

; alpha-vary : Expr -> Expr
; TODO: why does this need to throw errors for unbound ids?
;   I guess otherwise ((compose infer-type parse) '(with (x 5) y))) would return a meta-type (inherited from y's unconstrained type)?
(define alpha-vary ((curry alpha-vary/helper) (make-immutable-hasheq)))
  ; TODO: test (manually)
    (test/exn (alpha-vary (parse '{with {x {+ x x}} 1})) "Type Error: Unbound identifier")
    ; TODO: manually test:
    ;   - '{with {x 1} {with {x {+ x x}} x}}
    ;   - currently passes

; generate-constraints : symbol Expr -> (listof Constraint)
; TODO: document this
(define (generate-constraints e-id e)
  (type-case Expr e
    [num (n) (list (eqc (t-var e-id) (t-num)))]
    [id (v) (list (eqc (t-var e-id) (t-var v)))]
    [bool (b) (list (eqc (t-var e-id) (t-bool)))]
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
    [iszero (arg)
      (local ([define arg-id (gensym 'iszero)]
              [define arg-c (generate-constraints arg-id arg)])
        (append
          (list (eqc (t-var e-id) (t-bool))
                (eqc (t-var arg-id) (t-num)))
          arg-c))]
    [bif (pred if-true if-false)
      (local ([define pred-id (gensym 'pred)]
              [define true-id (gensym 'if-true)]
              [define false-id (gensym 'if-false)]
              [define pred-c (generate-constraints pred-id pred)]
              [define true-c (generate-constraints true-id if-true)]
              [define false-c (generate-constraints false-id if-false)])
        (append
          (list (eqc (t-var pred-id) (t-bool))
                (eqc (t-var e-id) (t-var true-id))
                (eqc (t-var e-id) (t-var false-id)))
          pred-c
          true-c
          false-c))]
    [with (bound-id bound-body with-body)
      (local ([define b-body-id (gensym 'bound-body)]
              [define w-body-id (gensym 'with-body)]
              [define b-body-c (generate-constraints b-body-id bound-body)]
              [define w-body-c (generate-constraints w-body-id with-body)])
        (append
          (list (eqc (t-var e-id) (t-var w-body-id))
                (eqc (t-var bound-id) (t-var b-body-id)))
          b-body-c
          w-body-c))]
    [rec-with (bound-id bound-body with-body)
      (local (
              [define b-body-id (gensym 'rec-bound-body)]
              [define w-body-id (gensym 'rec-with-body)]
              [define b-body-c (generate-constraints b-body-id bound-body)]
              [define w-body-c (generate-constraints w-body-id with-body)]
              )
        (append
          (list (eqc (t-var e-id) (t-var w-body-id))
                (eqc (t-var bound-id) (t-var b-body-id)))
          b-body-c
          w-body-c))]
    [fun (arg-id body)
      (local ([define body-id (gensym 'body)]
              [define body-c (generate-constraints body-id body)])
        (append
          (list (eqc (t-var e-id) (t-fun (t-var arg-id) (t-var body-id))))
          body-c))]
    [app (fun-expr arg-expr)
      (local ([define alpha-id (gensym 'alpha)]
              [define fun-id (gensym 'fun-expr)]
              [define arg-id (gensym 'arg-expr)]
              [define fun-c (generate-constraints fun-id fun-expr)]
              [define arg-c (generate-constraints arg-id arg-expr)])
        (append
          (list (eqc (t-var e-id) (t-var alpha-id))
                (eqc (t-var fun-id) (t-fun (t-var arg-id) (t-var alpha-id))))
          fun-c
          arg-c))]
    [tempty ()
      (list (eqc (t-var e-id) (t-list (t-var (gensym 'alpha)))))]
    [tcons (fst rst)
      (local ([define alpha-id (gensym 'alpha)]
              [define fst-id (gensym 'fst)]
              [define rst-id (gensym 'rst)]
              [define fst-c (generate-constraints fst-id fst)]
              [define rst-c (generate-constraints rst-id rst)])
        (append
          (list (eqc (t-var e-id) (t-list (t-var alpha-id)))
                (eqc (t-var fst-id) (t-var alpha-id))
                (eqc (t-var rst-id) (t-list (t-var alpha-id))))
          fst-c
          rst-c))]
    [tfirst (lst)
      (local ([define alpha-id (gensym 'alpha)]
              [define lst-id (gensym 'lst)]
              [define lst-c (generate-constraints lst-id lst)])
        (append
          (list (eqc (t-var e-id) (t-var alpha-id))
                (eqc (t-var lst-id) (t-list (t-var alpha-id))))
          lst-c))]
    [trest (lst)
      (local ([define alpha-id (gensym 'alpha)]
              [define lst-id (gensym 'lst)]
              [define lst-c (generate-constraints lst-id lst)])
        (append
          (list (eqc (t-var e-id) (t-list (t-var alpha-id)))
                (eqc (t-var lst-id) (t-list (t-var alpha-id))))
          lst-c))]
    [istempty (lst)
      (local ([define lst-id (gensym 'lst)]
              [define lst-c (generate-constraints lst-id lst)])
        (append
          (list (eqc (t-var e-id) (t-bool))
                (eqc (t-var lst-id) (t-list (t-var (gensym 'alpha)))))
          lst-c))]))

; ; unify : (listof Constraint) -> (listof Constraint)
; ; TODO: document this
(define (unify loc)
  (reverse (unify/helper empty loc)))

; unify/helper : (listof Constraint) -> (listof Constraint)
; TODO: document this
(define (unify/helper subst loc)
  ; (printf "\n\nunify/helper \n\tsubst=~s\n\tloc=~s\n\n" subst loc)
  (match loc
    [(list) ; loc is empty
      subst]
    [(cons (eqc lhs rhs) tail) ; (? (listof Constraint?) tail)
      ; (printf "cons\n\n\n\n\n")
      ; subst-and-recurse : Type::t-var Type -> (listof Constraint)
      (define (subst-and-recurse var val)
        (let ([substd-subst (fmap-expand-subst subst var val)]
              [substd-tail (fmap-expand-subst tail var val)])
          (unify/helper (cons (eqc var val) substd-subst)
                        substd-tail)))
      (define (simple-recurse)
        (unify/helper subst tail))

      (type-case Type lhs
        [t-num ()
          (type-case Type rhs
            [t-num ()
              (simple-recurse)]
            [t-var (sym)
              (subst-and-recurse rhs lhs)]
            [else
              (error 'unify "Type Error: Unable to unify constraints")])]
        [t-bool ()
          (type-case Type rhs
            [t-bool ()
              (simple-recurse)]
            [t-var (sym)
              (subst-and-recurse rhs lhs)]
            [else
              (error 'unify "Type Error: Unable to unify constraints")])]
        [t-list (elem-type)
          (type-case Type rhs
            [t-var (v)
              (subst-and-recurse rhs lhs)]
            [t-list (alpha)
              (let ([new-tail (cons (eqc elem-type alpha)
                                    tail)])
                (unify/helper subst new-tail))]
            [else
              (error 'unify "Type Error: Unable to unify constrapints")])]
        [t-fun (arg-type result-type)
          (type-case Type rhs
            [t-var (v)
              (subst-and-recurse rhs lhs)]
            [t-fun (alpha beta)
              (let ([new-tail (cons (eqc arg-type alpha)
                                    (cons (eqc result-type beta)
                                          tail))])
                (unify/helper subst new-tail))]
            [else
              (error 'unify "Type Error: Unable to unify constraints")])]
        [t-var (v)
          (if (equal? lhs rhs)
              (simple-recurse) ; ignore contraints like num = num or alpha = alpha
              (subst-and-recurse lhs rhs))])]))

; fmap-expand-subst : (or (listof Constraint) Constraint Type) Type::t-var Type -> (or (listof Constraint) Constraint Type)
; inspired by haskell's fmap function
(define (fmap-expand-subst obj target-type-var type-to-subst)
  (unless (t-var? target-type-var)
    (error 'unify "Internal Assertion Error: fmap-expand-subst not passed a t-var"))
  (define (simple-recurse new-obj)
    (fmap-expand-subst new-obj target-type-var type-to-subst))
  (match obj
    [(? (listof Constraint?) loc)
      (map simple-recurse loc)]
    [(eqc lhs rhs)
      (eqc (simple-recurse lhs)
           (simple-recurse rhs))]
    [(? Type? t)
      (type-case Type t
        [t-bool ()
          t]
        [t-num ()
          t]
        [t-var (sym)
          (if (equal? target-type-var t)
              type-to-subst
              t)]
        [t-list (alpha)
          (t-list (simple-recurse alpha))]
        [t-fun (alpha beta)
          (t-fun (simple-recurse alpha)
                 (simple-recurse beta))])]))
  ; basic tests
    (test/exn (fmap-expand-subst (t-num) (t-num) (t-num)) "Internal Assertion Error: fmap-expand-subst not passed a t-var")
    ; on Types
      (test (fmap-expand-subst (t-num) (t-var 'alpha) (t-num))
            (t-num))
      (test (fmap-expand-subst (t-var 'alpha) (t-var 'alpha) (t-num))
            (t-num))
      (test (fmap-expand-subst (t-var 'beta) (t-var 'alpha) (t-num))
            (t-var 'beta))
      (test (fmap-expand-subst (t-list (t-var 'alpha)) (t-var 'alpha) (t-num))
            (t-list (t-num)))
      (test (fmap-expand-subst (t-list (t-var 'beta)) (t-var 'alpha) (t-num))
            (t-list (t-var 'beta)))
      (test (fmap-expand-subst (t-fun (t-var 'alpha) (t-var 'beta)) (t-var 'alpha) (t-num))
            (t-fun (t-num) (t-var 'beta)))
      (test (fmap-expand-subst (t-fun (t-var 'beta) (t-var 'alpha)) (t-var 'alpha) (t-num))
            (t-fun (t-var 'beta) (t-num)))

      (test (fmap-expand-subst (t-var 'alpha) (t-var 'alpha) (t-var 'alpha))
            (t-var 'alpha))
    ; on Constraints
      (test (fmap-expand-subst (eqc (t-var 'alpha) (t-var 'beta)) (t-var 'alpha) (t-bool))
            (eqc (t-bool) (t-var 'beta)))
      (test (fmap-expand-subst (eqc (t-var 'beta) (t-var 'alpha)) (t-var 'alpha) (t-bool))
            (eqc (t-var 'beta) (t-bool)))

      (test (fmap-expand-subst (eqc (t-var 'alpha) (t-var 'alpha)) (t-var 'alpha) (t-var 'alpha))
            (eqc (t-var 'alpha) (t-var 'alpha)))
    ; on lists of Constraints
      (test (fmap-expand-subst (list (eqc (t-var 'alpha) (t-var 'beta))) (t-var 'alpha) (t-bool))
            (list (eqc (t-bool) (t-var 'beta))))
      (test (fmap-expand-subst (list (eqc (t-var 'beta) (t-var 'alpha))
                                       (eqc (t-var 'alpha) (t-var 'beta)))
                                 (t-var 'alpha) (t-bool))
            (list (eqc (t-var 'beta) (t-bool))
                  (eqc (t-bool) (t-var 'beta))))

; lookup-constraint : symbol (listof Constraint) -> Type
; TODO: document
(define (lookup-constraint target-name loc)
  (match loc
    [(list)
      (error 'infer-type "Internal Assertion Error: Could not find type of constraint")]
    [(cons (eqc (t-var current-name) current-value) tail)
      (if (equal? target-name current-name)
        current-value
        (lookup-constraint target-name tail))]))

; infer-type : Expr -> Type
; given an Expr, infers the type of the result or throws an error
(define (infer-type expr)
  (let ([result-sym (gensym 'result)])
    (lookup-constraint
      result-sym
      (unify (generate-constraints result-sym (alpha-vary expr))))))
  ; TODO: no idea whether this function will work

  ; tests
    ; TODO: test infer-type



; pipeline tests
  ; basic tests
    (define num-test-str '1)
    (define num-test-exp (num 1))
    (define num-test-constraints
      (list (eqc (t-var 'top) (t-num))))
    (define num-test-unified-constraints
      num-test-constraints)
    (test (parse num-test-str) num-test-exp)
    (test/pred (generate-constraints (gensym 'top) num-test-exp)
               (constraint-list=? num-test-constraints))
    (test/pred (unify num-test-constraints)
               (constraint-list=? num-test-unified-constraints))
    (test/pred (infer-type num-test-exp)
               (type=? (t-num)))

    (define id-test-str 'x)
    (define id-test-exp (id 'x))
    (define id-test-constraints
      (list (eqc (t-var 'top) (t-var 'x))))
    (define id-test-unified-constraints
      id-test-constraints)
    (test (parse id-test-str) id-test-exp)
    (test/pred (generate-constraints (gensym 'top) id-test-exp)
               (constraint-list=? id-test-constraints))
    (test/pred (unify id-test-constraints)
               (constraint-list=? id-test-unified-constraints))
    (test/exn (infer-type id-test-exp)
              "Type Error: Unbound identifier")

    (define plus-test-str '{+ 1 2})
    (define plus-test-exp (bin-num-op + (num 1) (num 2)))
    (define plus-test-constraints
      (list (eqc (t-var 'top) (t-num))
            (eqc (t-var 'lhs) (t-num))
            (eqc (t-var 'rhs) (t-num))
            (eqc (t-var 'lhs) (t-num))
            (eqc (t-var 'rhs) (t-num))))
    (define plus-test-unified-constraints
      (list (eqc (t-var 'top) (t-num))
            (eqc (t-var 'lhs) (t-num))
            (eqc (t-var 'rhs) (t-num))))
    (test (parse plus-test-str) plus-test-exp)
    (test/pred (generate-constraints (gensym 'top) plus-test-exp)
               (constraint-list=? plus-test-constraints))
    (test/pred (unify plus-test-constraints)
               (constraint-list=? plus-test-unified-constraints))
    (test/pred (infer-type plus-test-exp)
               (type=? (t-num)))

    (define minus-test-str '{- 1 2})
    (define minus-test-exp (bin-num-op - (num 1) (num 2)))
    (define minus-test-constraints
      (list (eqc (t-var 'top) (t-num))
            (eqc (t-var 'lhs) (t-num))
            (eqc (t-var 'rhs) (t-num))
            (eqc (t-var 'lhs) (t-num))
            (eqc (t-var 'rhs) (t-num))))
    (define minus-test-unified-constraints
      (list (eqc (t-var 'top) (t-num))
            (eqc (t-var 'lhs) (t-num))
            (eqc (t-var 'rhs) (t-num))))
    (test (parse minus-test-str) minus-test-exp)
    (test/pred (generate-constraints (gensym 'top) minus-test-exp)
               (constraint-list=? minus-test-constraints))
    (test/pred (unify minus-test-constraints)
               (constraint-list=? minus-test-unified-constraints))
    (test/pred (infer-type minus-test-exp)
               (type=? (t-num)))

    (define times-test-str '{* 1 2})
    (define times-test-exp (bin-num-op * (num 1) (num 2)))
    (define times-test-constraints
      (list (eqc (t-var 'top) (t-num))
            (eqc (t-var 'lhs) (t-num))
            (eqc (t-var 'rhs) (t-num))
            (eqc (t-var 'lhs) (t-num))
            (eqc (t-var 'rhs) (t-num))))
    (define times-test-unified-constraints
      (list (eqc (t-var 'top) (t-num))
            (eqc (t-var 'lhs) (t-num))
            (eqc (t-var 'rhs) (t-num))))
    (test (parse times-test-str) times-test-exp)
    (test/pred (generate-constraints (gensym 'top) times-test-exp)
               (constraint-list=? times-test-constraints))
    (test/pred (unify times-test-constraints)
               (constraint-list=? times-test-unified-constraints))
    (test/pred (infer-type times-test-exp)
               (type=? (t-num)))

    (define bool-test-str 'false)
    (define bool-test-exp (bool false))
    (define bool-test-constraints
      (list (eqc (t-var 'top) (t-bool))))
    (test (parse bool-test-str) bool-test-exp)
    (test/pred (generate-constraints (gensym 'top) bool-test-exp)
               (constraint-list=? bool-test-constraints))
    (test/pred (infer-type bool-test-exp)
               (type=? (t-bool)))

    (define iszero-test-str '{iszero 5})
    (define iszero-test-exp (iszero (num 5)))
    (define iszero-test-constraints
      (list (eqc (t-var 'top) (t-bool))
            (eqc (t-var 'arg) (t-num))
            (eqc (t-var 'arg) (t-num))))
    (define iszero-test-unified-constraints
      (list (eqc (t-var 'top) (t-bool))
            (eqc (t-var 'arg) (t-num))))
    (test (parse iszero-test-str) iszero-test-exp)
    (test/pred (generate-constraints (gensym 'top) iszero-test-exp)
               (constraint-list=? iszero-test-constraints))
    (test/pred (unify iszero-test-constraints)
               (constraint-list=? iszero-test-unified-constraints))
    (test/pred (infer-type iszero-test-exp)
               (type=? (t-bool)))

    ; should not find type errors until we run unify
    (define notypeerror-test-str2 '{iszero true})
    (define notypeerror-test-exp2 (iszero (bool true)))
    (define notypeerror-test-constraints2
      (list (eqc (t-var 'top) (t-bool))
            (eqc (t-var 'arg) (t-num))
            (eqc (t-var 'arg) (t-bool))))
    (test (parse notypeerror-test-str2) notypeerror-test-exp2)
    (test/pred (generate-constraints (gensym 'top) notypeerror-test-exp2)
               (constraint-list=? notypeerror-test-constraints2))
    (test/exn (unify notypeerror-test-constraints2)
              "Type Error: Unable to unify constraints")
    (test/exn (infer-type notypeerror-test-exp2)
              "Type Error: Unable to unify constraints")

    (define bif-test-str '{bif true 1 2})
    (define bif-test-exp (bif (bool true) (num 1) (num 2)))
    (define bif-test-constraints
      (list (eqc (t-var 'pred) (t-bool))
            (eqc (t-var 'top) (t-var 'if-true))
            (eqc (t-var 'top) (t-var 'if-false))
            (eqc (t-var 'pred) (t-bool))
            (eqc (t-var 'if-true) (t-num))
            (eqc (t-var 'if-false) (t-num))))
    (define bif-test-unified-constraints
      (list (eqc (t-var 'pred) (t-bool))
            (eqc (t-var 'top) (t-num))
            (eqc (t-var 'if-true) (t-num))
            (eqc (t-var 'if-false) (t-num))))
    (test (parse bif-test-str) bif-test-exp)
    (test/pred (generate-constraints (gensym 'top) bif-test-exp)
               (constraint-list=? bif-test-constraints))
    (test/pred (unify bif-test-constraints)
               (constraint-list=? bif-test-unified-constraints))
    (test/pred (infer-type bif-test-exp)
               (type=? (t-num)))

    (define with-test1-str '{with {x 1} 2})
    (define with-test1-exp (with 'x (num 1) (num 2)))
    (define with-test1-constraints
      (list (eqc (t-var 'top) (t-var 'with-body))
            (eqc (t-var 'x) (t-var 'bound-expr))
            (eqc (t-var 'bound-expr) (t-num))
            (eqc (t-var 'with-body) (t-num))))
    (define with-test1-unified-constraints
      (list (eqc (t-var 'top) (t-num))
            (eqc (t-var 'x) (t-num))
            (eqc (t-var 'bound-expr) (t-num))
            (eqc (t-var 'with-body) (t-num))))
    (test (parse with-test1-str) with-test1-exp)
    (test/pred (generate-constraints (gensym 'top) with-test1-exp)
               (constraint-list=? with-test1-constraints))
    (test/pred (unify with-test1-constraints)
               (constraint-list=? with-test1-unified-constraints))
    (test/pred (infer-type with-test1-exp)
               (type=? (t-num)))

    ; TODO s/+xx/iszero x/
    ; In this test, the constraints should conflate both x's into a single type, because we haven't run alpha-vary on the expression beforehand.
    (define with-test2-str '{with {x 1} {with {x {+ x x}} x}})
    (define with-test2-exp (with 'x (num 1) (with 'x (bin-num-op + (id 'x) (id 'x)) (id 'x))))
    (define with-test2-constraints
      (list (eqc (t-var 'top) (t-var 'outer-with-body))
              (eqc (t-var 'x) (t-var 'outer-bound-expr))
              (eqc (t-var 'outer-bound-expr) (t-num))
              (eqc (t-var 'outer-with-body) (t-var 'inner-with-body))
                (eqc (t-var 'x) (t-var 'inner-bound-expr))
                (eqc (t-var 'inner-bound-expr) (t-num))
                  (eqc (t-var 'inner-lhs) (t-num))
                  (eqc (t-var 'inner-rhs) (t-num))
                  (eqc (t-var 'inner-lhs) (t-var 'x))
                  (eqc (t-var 'inner-rhs) (t-var 'x))
                (eqc (t-var 'inner-with-body) (t-var 'x))))
    ; (define with-test2-unified-constraints
    ;   (list
    ;         (eqc () ())
    ;         ))
    (test (parse with-test2-str) with-test2-exp)
    (test/pred (generate-constraints (gensym 'top) with-test2-exp)
               (constraint-list=? with-test2-constraints))
    ; (test/pred (unify with-test2-constraints)
    ;            (constraint-list=? with-test2-unified-constraints))
    ; (test/pred (infer-type with-test1-exp)
    ;            (type=? (t-num)))

    (define recwith-test1-str '{rec {f {fun {x} 1}} 2})
    (define recwith-test1-exp (rec-with 'f (fun 'x (num 1)) (num 2)))
    (define recwith-test1-constraints
      (list (eqc (t-var 'top) (t-var 'with-body))
            (eqc (t-var 'f) (t-var 'bind-body))
            (eqc (t-var 'bind-body) (t-fun (t-var 'x) (t-var 'fun-body)))

            (eqc (t-var 'fun-body) (t-num))
            (eqc (t-var 'with-body) (t-num))))
    (define recwith-test1-unified-constraints
      (list (eqc (t-var 'top) (t-num))
            (eqc (t-var 'f) (t-fun (t-var 'x) (t-num)))
            (eqc (t-var 'bind-body) (t-fun (t-var 'x) (t-num)))

            (eqc (t-var 'fun-body) (t-num))
            (eqc (t-var 'with-body) (t-num))))
    (test (parse recwith-test1-str) recwith-test1-exp)
    (test/pred (generate-constraints (gensym 'top) recwith-test1-exp)
               (constraint-list=? recwith-test1-constraints))
    (test/pred (unify recwith-test1-constraints)
               (constraint-list=? recwith-test1-unified-constraints))
    (test/pred (infer-type recwith-test1-exp)
               (type=? (t-num)))

    (define recwith-test2-str '{rec {f {fun {x} {f x}}} {f 2}})
    (define recwith-test2-exp (rec-with 'f (fun 'x (app (id 'f) (id 'x))) (app (id 'f) (num 2))))
    (define recwith-test2-constraints
      (list (eqc (t-var 'top) (t-var 'with-body))
            (eqc (t-var 'f) (t-var 'bind-body))
            (eqc (t-var 'bind-body) (t-fun (t-var 'x) (t-var 'fun-body)))

            (eqc (t-var 'fun-body) (t-var 'alpha))
            (eqc (t-var 'fun-body-f) (t-fun (t-var 'inner-arg) (t-var 'alpha)))
              (eqc (t-var 'fun-body-f) (t-var 'f))
              (eqc (t-var 'inner-arg) (t-var 'x))

            (eqc (t-var 'with-body) (t-var 'beta))
            (eqc (t-var 'with-body-f) (t-fun (t-var 'outer-arg) (t-var 'beta)))
              (eqc (t-var 'with-body-f) (t-var 'f))
              (eqc (t-var 'outer-arg) (t-num))))
    (define recwith-test2-unified-constraints
      (list (eqc (t-var 'top) (t-var 'beta))
            (eqc (t-var 'f) (t-fun (t-num) (t-var 'beta)))
            (eqc (t-var 'bind-body) (t-fun (t-num) (t-var 'beta)))

            (eqc (t-var 'fun-body) (t-var 'beta))
            (eqc (t-var 'fun-body-f) (t-fun (t-num) (t-var 'beta)))
            (eqc (t-var 'inner-arg) (t-num))

            (eqc (t-var 'with-body) (t-var 'beta))
            (eqc (t-var 'with-body-f) (t-fun (t-num) (t-var 'beta)))
            (eqc (t-var 'outer-arg) (t-num))
            (eqc (t-var 'alpha) (t-var 'beta))
            (eqc (t-var 'x) (t-num))))
    (test (parse recwith-test2-str) recwith-test2-exp)
    (test/pred (generate-constraints (gensym 'top) recwith-test2-exp)
               (constraint-list=? recwith-test2-constraints))
    (test/pred (unify recwith-test2-constraints)
               (constraint-list=? recwith-test2-unified-constraints))
    (test/pred (infer-type recwith-test2-exp)
               (type=? (t-var 'beta)))

    ; TODO: test {rec {my-list {tcons 1 my-list}} my-list} ? Wait for TA response

    (define fun-test1-str '{fun {x} 2})
    (define fun-test1-exp (fun 'x (num 2)))
    (define fun-test1-constraints
      (list (eqc (t-var 'top) (t-fun (t-var 'x) (t-var 'body)))
            (eqc (t-var 'body) (t-num))))
    (define fun-test1-unified-constraints
      (list (eqc (t-var 'top) (t-fun (t-var 'x) (t-num)))
            (eqc (t-var 'body) (t-num))))
    (test (parse fun-test1-str) fun-test1-exp)
    (test/pred (generate-constraints (gensym 'top) fun-test1-exp)
               (constraint-list=? fun-test1-constraints))
    (test/pred (unify fun-test1-constraints)
               (constraint-list=? fun-test1-unified-constraints))
    (test/pred (infer-type fun-test1-exp)
               (type=? (t-fun (t-var 'alpha) (t-num))))

    (define fun-test2-str '{fun {x} {+ x 1}})
    (define fun-test2-exp (fun 'x (bin-num-op + (id 'x) (num 1))))
    (define fun-test2-constraints
      (list (eqc (t-var 'top) (t-fun (t-var 'x) (t-var 'body)))
            (eqc (t-var 'body) (t-num))
            (eqc (t-var 'lhs) (t-num))
            (eqc (t-var 'rhs) (t-num))
            (eqc (t-var 'lhs) (t-var 'x))
            (eqc (t-var 'rhs) (t-num))))
    (define fun-test2-unified-constraints
      (list (eqc (t-var 'top) (t-fun (t-num) (t-num)))
            (eqc (t-var 'body) (t-num))
            (eqc (t-var 'lhs) (t-num))
            (eqc (t-var 'rhs) (t-num))
            (eqc (t-var 'x) (t-num))))
    (test (parse fun-test2-str) fun-test2-exp)
    (test/pred (generate-constraints (gensym 'top) fun-test2-exp)
               (constraint-list=? fun-test2-constraints))
    (test/pred (unify fun-test2-constraints)
               (constraint-list=? fun-test2-unified-constraints))
    (test/pred (infer-type fun-test2-exp)
               (type=? (t-fun (t-num) (t-num))))

    (define app-test-str '{f 1})
    (define app-test-exp (app (id 'f) (num 1)))
    (define app-test-constraints
      (list (eqc (t-var 'top) (t-var 'alpha))
            (eqc (t-var 'function) (t-fun (t-var 'arg) (t-var 'alpha)))
            (eqc (t-var 'function) (t-var 'f))
            (eqc (t-var 'arg) (t-num))))
    (define app-test-unified-constraints
      (list (eqc (t-var 'top) (t-var 'alpha))
            (eqc (t-var 'function) (t-fun (t-num) (t-var 'alpha)))
            (eqc (t-var 'f) (t-fun (t-num) (t-var 'alpha)))
            (eqc (t-var 'arg) (t-num))))
    (test (parse app-test-str) app-test-exp)
    (test/pred (generate-constraints (gensym 'top) app-test-exp)
               (constraint-list=? app-test-constraints))
    (test/pred (unify app-test-constraints)
               (constraint-list=? app-test-unified-constraints))
    (test/exn (infer-type app-test-exp)
              "Type Error: Unbound identifier")

    (define tempty-test-str 'tempty)
    (define tempty-test-exp (tempty))
    (define tempty-test-constraints
      (list (eqc (t-var 'top) (t-list (t-var 'alpha)))))
    (define tempty-test-unified-constraints
      tempty-test-constraints)
    (test (parse tempty-test-str) tempty-test-exp)
    (test/pred (generate-constraints (gensym 'top) tempty-test-exp)
               (constraint-list=? tempty-test-constraints))
    (test/pred (unify tempty-test-constraints)
               (constraint-list=? tempty-test-unified-constraints))
    (test/pred (infer-type tempty-test-exp)
               (type=? (t-list (t-var 'alpha))))

    (define tcons-test-str '{tcons 1 tempty})
    (define tcons-test-exp (tcons (num 1) (tempty)))
    (define tcons-test-constraints
      (list (eqc (t-var 'top) (t-list (t-var 'alpha)))
            (eqc (t-var 'fst) (t-var 'alpha))
            (eqc (t-var 'rst) (t-list (t-var 'alpha)))
            (eqc (t-var 'fst) (t-num))
            (eqc (t-var 'rst) (t-list (t-var 'beta)))))
    (define tcons-test-unified-constraints
      (list (eqc (t-var 'top) (t-list (t-num)))
            (eqc (t-var 'fst) (t-num))
            (eqc (t-var 'rst) (t-list (t-num)))
            (eqc (t-var 'alpha) (t-num))
            (eqc (t-var 'beta) (t-num))))
    (test (parse tcons-test-str) tcons-test-exp)
    (test/pred (generate-constraints (gensym 'top) tcons-test-exp)
               (constraint-list=? tcons-test-constraints))
    (test/pred (unify tcons-test-constraints)
               (constraint-list=? tcons-test-unified-constraints))
    (test/pred (infer-type tcons-test-exp)
               (type=? (t-list (t-num))))

    (define tfirst-test1-str '{tfirst tempty})
    (define tfirst-test1-exp (tfirst (tempty)))
    (define tfirst-test1-constraints
      (list (eqc (t-var 'top) (t-var 'alpha))
            (eqc (t-var 'lst) (t-list (t-var 'alpha)))
            (eqc (t-var 'lst) (t-list (t-var 'beta)))))
    (define tfirst-test1-unified-constraints
      (list (eqc (t-var 'top) (t-var 'alpha))
            (eqc (t-var 'lst) (t-list (t-var 'alpha)))
            (eqc (t-var 'beta) (t-var 'alpha))))
    (test (parse tfirst-test1-str) tfirst-test1-exp)
    (test/pred (generate-constraints (gensym 'top) tfirst-test1-exp)
               (constraint-list=? tfirst-test1-constraints))
    (test/pred (unify tfirst-test1-constraints)
               (constraint-list=? tfirst-test1-unified-constraints))
    (test/pred (infer-type tfirst-test1-exp)
               (type=? (t-var 'alpha)))

    (define tfirst-test2-str '{tfirst {tcons 1 tempty}})
    (define tfirst-test2-exp (tfirst (tcons (num 1) (tempty))))
    (define tfirst-test2-constraints
      (list (eqc (t-var 'top) (t-var 'alpha))
            (eqc (t-var 'lst) (t-list (t-var 'alpha)))

            (eqc (t-var 'lst) (t-list (t-var 'beta)))
            (eqc (t-var 'fst) (t-var 'beta))
            (eqc (t-var 'rst) (t-list (t-var 'beta)))

            (eqc (t-var 'fst) (t-num))
            (eqc (t-var 'rst) (t-list (t-var 'gamma)))))
    (define tfirst-test2-unified-constraints
      (list (eqc (t-var 'top) (t-num))
            (eqc (t-var 'lst) (t-list (t-num)))
            (eqc (t-var 'alpha) (t-num))
            (eqc (t-var 'fst) (t-num))
            (eqc (t-var 'rst) (t-list (t-num)))
            (eqc (t-var 'beta) (t-num))
            (eqc (t-var 'gamma) (t-num))))
    (test (parse tfirst-test2-str) tfirst-test2-exp)
    (test/pred (generate-constraints (gensym 'top) tfirst-test2-exp)
               (constraint-list=? tfirst-test2-constraints))
    (test/pred (unify tfirst-test2-constraints)
               (constraint-list=? tfirst-test2-unified-constraints))
    (test/pred (infer-type tfirst-test2-exp)
               (type=? (t-num)))

    (define trest-test1-str '{trest tempty})
    (define trest-test1-exp (trest (tempty)))
    (define trest-test1-constraints
      (list (eqc (t-var 'top) (t-list (t-var 'alpha)))
            (eqc (t-var 'lst) (t-list (t-var 'alpha)))
            (eqc (t-var 'lst) (t-list (t-var 'beta)))))
    (define trest-test1-unified-constraints
      (list (eqc (t-var 'top) (t-list (t-var 'alpha)))
            (eqc (t-var 'lst) (t-list (t-var 'alpha)))
            (eqc (t-var 'beta) (t-var 'alpha))))
    (test (parse trest-test1-str) trest-test1-exp)
    (test/pred (generate-constraints (gensym 'top) trest-test1-exp)
               (constraint-list=? trest-test1-constraints))
    (test/pred (unify trest-test1-constraints)
               (constraint-list=? trest-test1-unified-constraints))
    (test/pred (infer-type trest-test1-exp)
               (type=? (t-list (t-var 'alpha))))

    (define trest-test2-str '{trest {tcons 1 tempty}})
    (define trest-test2-exp (trest (tcons (num 1) (tempty))))
    (define trest-test2-constraints
      (list (eqc (t-var 'top) (t-list (t-var 'alpha)))
            (eqc (t-var 'lst) (t-list (t-var 'alpha)))
            (eqc (t-var 'lst) (t-list (t-var 'beta)))
            (eqc (t-var 'fst) (t-var 'beta))
            (eqc (t-var 'rst) (t-list (t-var 'beta)))
            (eqc (t-var 'fst) (t-num))
            (eqc (t-var 'rst) (t-list (t-var 'gamma)))))
    (define trest-test2-unified-constraints
      (list (eqc (t-var 'top) (t-list (t-num)))
            (eqc (t-var 'lst) (t-list (t-num)))
            (eqc (t-var 'alpha) (t-num))
            (eqc (t-var 'fst) (t-num))
            (eqc (t-var 'rst) (t-list (t-num)))
            (eqc (t-var 'beta) (t-num))
            (eqc (t-var 'gamma) (t-num))))
    (test (parse trest-test2-str) trest-test2-exp)
    (test/pred (generate-constraints (gensym 'top) trest-test2-exp)
               (constraint-list=? trest-test2-constraints))
    (test/pred (unify trest-test2-constraints)
               (constraint-list=? trest-test2-unified-constraints))
    (test/pred (infer-type trest-test2-exp)
               (type=? (t-list (t-num))))

    (define tempty?-test1-str '{tempty? tempty})
    (define tempty?-test1-exp (istempty (tempty)))
    (define tempty?-test1-constraints
      (list (eqc (t-var 'top) (t-bool))
            (eqc (t-var 'lst) (t-list (t-var 'alpha)))
            (eqc (t-var 'lst) (t-list (t-var 'beta)))))
    (define tempty?-test1-unified-constraints
      (list (eqc (t-var 'top) (t-bool))
            (eqc (t-var 'lst) (t-list (t-var 'alpha)))
            (eqc (t-var 'beta) (t-var 'alpha))))
    (test (parse tempty?-test1-str) tempty?-test1-exp)
    (test/pred (generate-constraints (gensym 'top) tempty?-test1-exp)
               (constraint-list=? tempty?-test1-constraints))
    (test/pred (unify tempty?-test1-constraints)
               (constraint-list=? tempty?-test1-unified-constraints))
    (test/pred (infer-type tempty?-test1-exp)
               (type=? (t-bool)))

    (define tempty?-test2-str '{tempty? {tcons 1 tempty}})
    (define tempty?-test2-exp (istempty (tcons (num 1) (tempty))))
    (define tempty?-test2-constraints
      (list (eqc (t-var 'top) (t-bool))
            (eqc (t-var 'lst) (t-list (t-var 'alpha)))

            (eqc (t-var 'lst) (t-list (t-var 'beta)))
            (eqc (t-var 'fst) (t-var 'beta))
            (eqc (t-var 'rst) (t-list (t-var 'beta)))

            (eqc (t-var 'fst) (t-num))
            (eqc (t-var 'rst) (t-list (t-var 'gamma)))))
    (define tempty?-test2-unified-constraints
      (list (eqc (t-var 'top) (t-bool))
            (eqc (t-var 'lst) (t-list (t-num)))
            (eqc (t-var 'alpha) (t-num))
            (eqc (t-var 'fst) (t-num))
            (eqc (t-var 'rst) (t-list (t-num)))
            (eqc (t-var 'beta) (t-num))
            (eqc (t-var 'gamma) (t-num))))
    (test (parse tempty?-test2-str) tempty?-test2-exp)
    (test/pred (generate-constraints (gensym 'top) tempty?-test2-exp)
               (constraint-list=? tempty?-test2-constraints))
    (test/pred (unify tempty?-test2-constraints)
               (constraint-list=? tempty?-test2-unified-constraints))
    (test/pred (infer-type tempty?-test2-exp)
               (type=? (t-bool)))

  ; TODO: extensive tests







; TODO: is this true? wait for response to https://groups.google.com/forum/#!topic/byu-cs-330-fall-2015/sFLnnq04Gc8
;   (test (infer-type (parse '{rec {my-list {tcons 1 my-list}} my-list}))
;         (t-list (t-num)))
;   TODO: also, make sure that with doesn't accidentally behave like rec-with

;   TODO: make sure rec-with is implemented correctly for alpha-vary and generate constraints



; TODO: look at the "testing hints" section on the assignment details page
  ; TODO: including "Make sure you have test cases for the occurs check [PLAI 282]."
; TODO: extra credit


