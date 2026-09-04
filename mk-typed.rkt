#lang typed/racket

(provide (all-defined-out))


;;--------------------- substitution ----------------------

(struct var ([name : Symbol]) #:transparent)

(define-type Var var)
(define-type Atom (U Symbol String Number Boolean Char Bytes Keyword Null))
(define-type Term (U Var Atom (Pairof Term Term)))
(define-type S (Listof (Pairof Var Term)))

(: empty-s S)
(define empty-s '())

(: size-s (-> S Index))
(define size-s length)

(: ext-s (-> Var Term S S))
(define ext-s
  (lambda (x v s)
    (cons `(,x . ,v) s)))

(: walk (-> Term S Term))
(define walk
  (lambda (v s)
    (cond
      [(var? v)
       (let ([p (assq v s)])
         (cond
           [(not p) v]
           [else
            (walk (cdr p) s)]))]
      [else v])))

(: walk* (-> Term S Term))
(define walk*
  (lambda (v s)
    (let ([v (walk v s)])
      (cond
        [(var? v) v]
        [(pair? v)
         (cons
          (walk* (car v) s)
          (walk* (cdr v) s))]
        [else v]))))

(: unify (-> Term Term S (Option S)))
(define unify
  (lambda (u v s)
    (let ([u (walk u s)]
          [v (walk v s)])
      (cond
        [(eq? u v) s]
        [(var? u) (ext-s u v s)]
        [(var? v) (ext-s v u s)]
        [(and (pair? u) (pair? v))
         (let ([s (unify (car u) (car v) s)])
           (and s (unify (cdr u) (cdr v) s)))]
        [(equal? u v) s]
        [else #f]))))

(: name-prefix String)
(define name-prefix "_")

(: set-name-prefix (-> String Void))
(define set-name-prefix
  (lambda (s)
    (set! name-prefix s)))

(: name (-> Integer Symbol))
(define name
  (lambda (n)
    (string->symbol
     (string-append name-prefix (number->string n)))))

(: reify-s (-> Term S S))
(define reify-s
  (lambda (v s)
    (let ([v (walk v s)])
      (cond
        [(var? v)
         (ext-s v (name (size-s s)) s)]
        [(pair? v)
         (reify-s (cdr v)
                  (reify-s (car v) s))]
        [else s]))))

(: reify (-> Term S Term))
(define reify
  (lambda (v s)
    (let ([v (walk* v s)])
      (walk* v (reify-s v empty-s)))))


;;---------------------- composition ----------------------

;; The stream is parameterised by what it carries; a goal instantiates
;; it at `S', so a goal maps a substitution to a stream of substitutions.
(struct (A) stream ([head : A] [tail : (Stream A)]) #:transparent)
(struct (A) thunk ([func : (-> (Stream A))]) #:transparent)

(define-type (Stream A) (U Null (thunk A) (stream A)))
(define-type Goal (-> S (Stream S)))

(define-syntax delay
  (syntax-rules ()
    [(_ e ...)
     (thunk (lambda () e ...))]))

(: force (All (A) (-> (Stream A) (Stream A))))
(define force
  (lambda (th)
    (match th
      [(thunk f) (f)]
      [_ th])))

(: bind (All (A B) (-> (-> A (Stream B)) (Stream A) (Stream B))))
(define bind
  (lambda (g v)
    (match v
      ['() '()]
      [(thunk _)
       (delay (bind g (force v)))]
      [(stream head tail)
       (mplus (g head) (delay (bind g tail)))])))

#;(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bind* (bind e g0) g ...))))

(: bind* (-> (Stream S) Goal * (Stream S)))
(define bind*
  (lambda (v . gs)
    ;; (foldl bind v gs)
    (cond
      [(null? gs) v]
      [else
       (apply bind* (bind (car gs) v) (cdr gs))])))

(: mplus (All (A) (-> (Stream A) (Stream A) (Stream A))))
(define mplus
  (lambda (v f)
    (match v
      ['() f]
      [(thunk _)
       (delay (mplus f (force v)))]
      [(stream head tail)
       (stream head (delay (mplus f tail)))])))

#;(define-syntax mplus*
  (syntax-rules ()
    [(_ e) e]
    [(_ e0 e ...)
     (mplus e0 (delay (mplus* e ...)))]))

(: mplus* (All (A) (-> (Stream A) (Stream A) * (Stream A))))
(define mplus*
  (lambda (e . res)
    (cond
     [(null? res) e]
     [else
      (mplus e (delay (apply mplus* (car res) (cdr res))))])))


;;------------------- goal constructors -------------------

(: succeed Goal)
(define succeed
  (lambda (s) (stream s '())))

(: fail Goal)
(define fail
  (lambda (s) '()))

(: == (-> Term Term Goal))
(define ==
  (lambda (u v)
    (lambda (s)
      (delay
        (let ([s^ (unify u v s)])
          (if s^ (succeed s^) (fail s)))))))

(define-syntax exist
  (syntax-rules ()
    [(_ (x ...) g0 g ...)
     (lambda ([s : S]) : (Stream S)
       (delay
         (let ([x (var 'x)] ...)
           (bind* (succeed s) g0 g ...))))]))

(define-syntax conde
  (syntax-rules ()
    [(_ [g0 g ...]
        [g1 g^ ...] ...)
     (lambda ([s : S]) : (Stream S)
       (delay
         (mplus*
          (bind* (succeed s) g0 g ...)
          (bind* (succeed s) g1 g^ ...) ...)))]))

(define-syntax trace
  (syntax-rules ()
    [(_ msg v ...)
     (lambda ([s : S]) : (Stream S)
       (printf "~a~a: ~a~n" msg 'v (reify v s)) ...
       (succeed s))]))


;;----------------------- top level -----------------------

(: take (All (A) (-> Real (Stream A) (Listof A))))
(define take
  (lambda (n v)
    (cond
      [(zero? n) '()]
      [else
       (match v
         ['() '()]
         [(thunk _)
          (take n (force v))]
         [(stream head tail)
          (cons head (take (- n 1) tail))])])))

(: do-display Boolean)
(define do-display #f)

(: display-code (-> Boolean Void))
(define display-code
  (lambda (v)
    (set! do-display v)))

(: debug-display (-> Real (Listof Any) Void))
(define debug-display
  (lambda (n contents)
    (cond
      [do-display
       (display "-----------------------------------\n")
       (if (= n +inf.0)
           (pretty-print `(run* ,@contents))
           (pretty-print `(run ,n ,@contents)))]
      [else (void)])))

;; `x' is bound outside the goal so that the answers can be reified
;; after they are taken from the stream: the stream a goal builds is a
;; `(Stream S)', so reification happens on the way out rather than in it.
(define-syntax run
  (syntax-rules ()
    [(_ n (x) g0 g ...)
     (begin
       (debug-display n '((x) g0 g ...))
       (let ([x (var 'x)])
         (map (lambda ([s : S]) (reify x s))
              (take n (delay (bind* (succeed empty-s) g0 g ...))))))]))

(define-syntax run*
  (syntax-rules ()
    [(_ (x) g ...)
     (run +inf.0 (x) g ...)]))
