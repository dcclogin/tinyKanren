#lang racket

;; Examples and tests for "mk.rkt", the Racket tinyKanren.
;;
;; Every case states the query, the expected answers as `reify' returns
;; them, and (for the divergent relations) the bound that makes the query
;; finite.  Running the module runs them all and reports.
;;
;;   racket examples.rkt

(require "mk.rkt")


;;------------------------- relations ------------------------

(define nullo
  (lambda (l)
    (== l '())))

(define conso
  (lambda (a d p)
    (== (cons a d) p)))

(define caro
  (lambda (p a)
    (exist (d) (conso a d p))))

(define cdro
  (lambda (p d)
    (exist (a) (conso a d p))))

(define appendo
  (lambda (l s out)
    (conde
      [(nullo l) (== s out)]
      [(exist (a d res)
         (conso a d l)
         (conso a res out)
         (appendo d s res))])))

(define membero
  (lambda (x l)
    (exist (a d)
      (conso a d l)
      (conde
        [(== x a)]
        [(membero x d)]))))

(define reverso
  (lambda (l out)
    (conde
      [(nullo l) (nullo out)]
      [(exist (a d res)
         (conso a d l)
         (reverso d res)
         (appendo res (list a) out))])))

;; Unary numbers: z, (s z), (s (s z)), ...
(define zero 'z)

(define succo
  (lambda (n)
    (list 's n)))

(define peano
  (lambda (n)
    (cond
      [(zero? n) zero]
      [else (succo (peano (- n 1)))])))

(define pluso
  (lambda (n m out)
    (conde
      [(== n zero) (== m out)]
      [(exist (n^ out^)
         (== n (succo n^))
         (== out (succo out^))
         (pluso n^ m out^))])))

;; The two relations that make interleaving observable: `alwayso'
;; succeeds infinitely often, `nevero' never succeeds and never stops.
;; Both are knots tied through `conde', whose `delay' keeps the recursive
;; occurrence unforced.
(define alwayso
  (conde
    [succeed]
    [alwayso]))

(define nevero
  (conde
    [nevero]))


;;--------------------------- cases ---------------------------

(struct kase (what got want) #:transparent)

(define-syntax-rule (case: what query want)
  (kase what query 'want))

(define cases
  (list
   ;;-------------------------------------------------- unification
   (case: "q is 5"
     (run* (q) (== q 5))
     (5))

   (case: "5 is q (symmetric)"
     (run* (q) (== 5 q))
     (5))

   (case: "no answers"
     (run* (q) fail)
     ())

   (case: "succeed leaves q fresh"
     (run* (q) succeed)
     (_0))

   (case: "conflicting equations fail"
     (run* (q) (== q 5) (== q 6))
     ())

   (case: "the same equation twice"
     (run* (q) (== q 5) (== q 5))
     (5))

   (case: "atoms of every kind"
     (run* (q) (== q (list 'a "b" 3 #t #f '())))
     ((a "b" 3 #t #f ())))

   (case: "an improper list"
     (run* (q) (== q (cons 1 2)))
     ((1 . 2)))

   (case: "structural unification"
     (run* (q) (exist (x y)
                 (== (list x 2) (list 1 y))
                 (== q (list x y))))
     ((1 2)))

   (case: "occurs freely: q is bound to a variable, not a value"
     (run* (q) (exist (x) (== q x)))
     (_0))

   ;;------------------------------------------------------- reify
   (case: "distinct fresh variables get distinct names"
     (run* (q) (exist (x y) (== q (list x y))))
     ((_0 _1)))

   (case: "sharing is visible in the reified answer"
     (run* (q) (exist (x y) (== q (list x y x))))
     ((_0 _1 _0)))

   (case: "a variable equated with another is reified once"
     (run* (q) (exist (x y) (== x y) (== q (list x y))))
     ((_0 _0)))

   (case: "reification walks under pairs"
     (run* (q) (exist (x y) (== q (cons (list x 1) y))))
     (((_0 1) . _1)))

   ;;------------------------------------------------------- conde
   (case: "three clauses, three answers"
     (run* (q) (conde [(== q 1)] [(== q 2)] [(== q 3)]))
     (1 2 3))

   (case: "a failing clause is skipped"
     (run* (q) (conde [fail] [(== q 2)] [fail] [(== q 4)]))
     (2 4))

   (case: "conde is a disjunction of conjunctions"
     (run* (q) (conde [(== q 1) fail] [(== q 2) succeed]))
     (2))

   ;; The four answers come out in the order the interleaving in `mplus'
   ;; produces them, which is not the clause order.
   (case: "nested conde multiplies the clauses"
     (run* (q) (exist (x y)
                 (conde [(== x 1)] [(== x 2)])
                 (conde [(== y 'a)] [(== y 'b)])
                 (== q (list x y))))
     ((1 a) (1 b) (2 a) (2 b)))

   ;;------------------------------------------------------- caro/cdro
   (case: "caro of a list"
     (run* (q) (caro '(a b c) q))
     (a))

   (case: "cdro of a list"
     (run* (q) (cdro '(a b c) q))
     ((b c)))

   (case: "caro run backwards builds a list"
     (run* (q) (caro q 'a) (cdro q '(b)))
     ((a b)))

   ;;------------------------------------------------------- appendo
   (case: "appendo forwards"
     (run* (q) (appendo '(1 2) '(3 4) q))
     ((1 2 3 4)))

   (case: "appendo with a fresh tail"
     (run* (q) (exist (x) (appendo '(1) x '(1 2)) (== q x)))
     ((2)))

   (case: "appendo backwards: every split of a three-element list"
     (run* (q) (exist (x y)
                 (appendo x y '(a b c))
                 (== q (list x y))))
     ((() (a b c))
      ((a) (b c))
      ((a b) (c))
      ((a b c) ())))

   (case: "appendo with both arguments fresh is infinite"
     (run 4 (q) (exist (x y z) (appendo x y z) (== q (list x y z))))
     ((() _0 _0)
      ((_0) _1 (_0 . _1))
      ((_0 _1) _2 (_0 _1 . _2))
      ((_0 _1 _2) _3 (_0 _1 _2 . _3))))

   ;;------------------------------------------------------- membero
   (case: "membero enumerates the elements"
     (run* (q) (membero q '(1 2 3)))
     (1 2 3))

   (case: "membero as a test: present"
     (run* (q) (membero 2 '(1 2 3)) (== q #t))
     (#t))

   (case: "membero as a test: absent"
     (run* (q) (membero 9 '(1 2 3)) (== q #t))
     ())

   (case: "membero repeats a repeated element"
     (run* (q) (membero q '(a b a)))
     (a b a))

   (case: "two memberos intersect"
     (run* (q) (membero q '(1 2 3)) (membero q '(3 4 1)))
     (1 3))

   (case: "membero of a fresh list is infinite"
     (run 3 (q) (membero 'x q))
     ((x . _0)
      (_0 x . _1)
      (_0 _1 x . _2)))

   ;;------------------------------------------------------- reverso
   (case: "reverso forwards"
     (run* (q) (reverso '(1 2 3) q))
     ((3 2 1)))

   (case: "reverso backwards"
     (run 1 (q) (reverso q '(1 2 3)))
     ((3 2 1)))

   ;;------------------------------------------------------- arithmetic
   (case: "2 + 3 = 5"
     (run* (q) (pluso (peano 2) (peano 3) q))
     ((s (s (s (s (s z)))))))

   (case: "5 - 2 = 3 (subtraction is addition backwards)"
     (run* (q) (pluso (peano 2) q (peano 5)))
     ((s (s (s z)))))

   (case: "every pair summing to 3"
     (run* (q) (exist (x y) (pluso x y (peano 3)) (== q (list x y))))
     ((z (s (s (s z))))
      ((s z) (s (s z)))
      ((s (s z)) (s z))
      ((s (s (s z))) z)))

   (case: "addition with both summands fresh is infinite"
     (run 3 (q) (exist (x y z) (pluso x y z) (== q (list x y z))))
     ((z _0 _0)
      ((s z) _0 (s _0))
      ((s (s z)) _0 (s (s _0)))))

   ;;------------------------------------------------------- interleaving
   (case: "run bounds an infinite stream"
     (run 3 (q) alwayso (== q #t))
     (#t #t #t))

   (case: "a finite branch is not starved by an infinite one"
     (run 3 (q) (conde [(== q #t)] [alwayso]) (== q #f))
     (#f #f #f))

   (case: "a divergent branch does not hide an answer in another"
     (run 1 (q) (conde [nevero] [(== q 'found)]))
     (found))

   (case: "a divergent branch on either side"
     (run 1 (q) (conde [(== q 'found)] [nevero]))
     (found))

   (case: "asking for none of an infinite stream terminates"
     (run 0 (q) alwayso)
     ())))


;;--------------------------- runner ---------------------------

(define show
  (lambda (ts)
    (string-join (map (lambda (t) (format "~s" t)) ts) " ")))

(define report
  (lambda (c)
    (match-define (kase what got want) c)
    (cond
      [(equal? got want)
       (printf "ok   ~a  =>  ~a\n" what (show got))
       #t]
      [else
       (printf "FAIL ~a\n" what)
       (printf "       want: ~a\n" (show want))
       (printf "       got:  ~a\n" (show got))
       #f])))

;; `trace' prints as a side effect, so it is shown rather than checked:
;; the goal itself only succeeds.
(define demo-trace
  (lambda ()
    (printf "\ntrace:\n")
    (println
     (run* (q)
       (exist (x y)
         (== x 1)
         (trace "  " x y)
         (== q (list x y)))))))

(module+ main
  (define results (map report cases))
  (define failed (length (filter not results)))
  (printf "\n~a / ~a passed\n" (- (length cases) failed) (length cases))
  (demo-trace)
  (unless (zero? failed) (exit 1)))
