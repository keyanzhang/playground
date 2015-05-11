#lang racket
(require racket/syntax)
(provide kmatch kmatch-who)

#|

A linear pattern matcher based on Oleg Kiselyov's `pmatch`[1].
The goal is to port `match.ss`[2]'s catamorphism[3] feature to `pmatch` while preserving its simplicity. 
Unsurprisingly it's called `kmatch`. https://github.com/keyanzhang/playground/kmatch.rkt

[1] pmatch: https://cgi.soic.indiana.edu/~c311/lib/exe/fetch.php?media=pmatch.pdf
[2] match: http://www.cs.indiana.edu/chezscheme/match/
[3] Catamorphism: http://en.wikipedia.org/wiki/Catamorphism

Exp    ::= (kmatch Exp Clause+)
         | (kmatch-who Name Exp Clause+)
         | OtherSchemeExp

Clause ::= (`Pat Exp+)
         | (`Pat (guard Exp*) Exp+)

Pat    ::= ()
         | (Pat ... . Pat)                 ;; @TODO
         | (Pat . Pat)
         | #(Pat* Pat ... Pat*)            ;; @TODO
         | #(Pat*)                         ;; @TODO
         | ,Id
         | ,[Id*]
         | ,[Cata -> Id*]
         | Id

Cata   ::= Exp

@DONE:
1. `,[]`, `,[Id*]`, `[Cata -> Id*]` functionalities (there are some test cases at the bottom of the file).

@TODO:
1. ellipsis ...
2. identical pattern variables: `(,a ,b ,a)
3. In CATA clauses, let `guard` make decision based on the initial (raw) value.

|#

(require (only-in rnrs/base-6
                  [let-values let-some-values]))

(define-syntax kmatch
  (syntax-rules ()
    [(_ val clause* ...)
     (kmatch-who #f val clause* ...)]))

(define-syntax kmatch-who
  (syntax-rules ()
    [(_ name (rator rand* ...) clause* ...)
     (let ([val (rator rand* ...)])
       (letrec ([self (lambda (x)
                        (kmatch-aux self '(rator rand* ...)
                                    name x clause* ...))])
         (kmatch-aux self '(rator rand* ...) name val clause* ...)))]
    [(_ name val clause* ...)
     (letrec ([self (lambda (x)
                      (kmatch-aux self 'val
                                  name x clause* ...))])
       (kmatch-aux self 'val name val clause* ...))]))

(define-syntax kmatch-aux
  (syntax-rules (else guard quasiquote)
    [(_ self input name val)
     (begin
       (if 'name
           (printf "; kmatch: ~s failure" 'name)
           (printf "; kmatch: failure"))
       (printf "; no matching clause for input ~s (evaluating to ~s)\n" input val)
       (error 'kmatch "failure"))]
    [(_ self input name val
        (else exp exp* ...))
     (begin exp exp* ...)]
    [(_ self input name val
        ((quasiquote pat) (guard g* ...) exp exp* ...)
        clause* ...)
     (let ([cont-fail (lambda ()
                        (kmatch-aux self input name val clause* ...))])
       (ppat val pat
             (if (and g* ...)
                 (begin exp exp* ...)
                 (cont-fail))
             (cont-fail)
             self))]
    [(_ self input name val
        ((quasiquote pat) exp exp* ...) clause* ...)
     (let ([cont-fail (lambda ()
                        (kmatch-aux self input name val clause* ...))])
       (ppat val pat
             (begin exp exp* ...)
             (cont-fail)
             self))]))

(define-syntax ppat
  (syntax-rules (unquote ->)
    ;; [(_ val _ cont-t cont-f)
    ;;  cont-t]
    [(_ val (unquote [cata -> v v* ...]) cont-t cont-f self)
     (let-some-values ([(v v* ... . _) (cata val)])
       cont-t)]
    [(_ val (unquote [cata ->]) cont-t cont-f self)
     (let-some-values ([(foo . _) (cata val)])
       cont-t)]
    [(_ val (unquote [v v* ...]) cont-t cont-f self)
     (let-some-values ([(v v* ... . _) (self val)])
       cont-t)]
    [(_ val (unquote []) cont-t cont-f self)
     (let-some-values ([(foo . _) (self val)])
       cont-t)]
    [(_ val (unquote var) cont-t cont-f self)
     (let ([var val])
       cont-t)]
    [(_ val (a . d) cont-t cont-f self)
     (if (pair? val)
         (let ([val-a (car val)] [val-d (cdr val)])
           (ppat val-a a
                 (ppat val-d d cont-t cont-f self)
                 cont-f
                 self))
         cont-f)]
    [(_ val const cont-t cont-f self) (if (equal? val (quote const)) cont-t cont-f)]))

;; (define nl1 '((1 2 3) (4 5)))
;; (define nl2 '(((1 2 3) (4 5)) ((6 7))))

;; `(start ,nl1 end) ;; => '(start ((1 2 3) (4 5)) end)
;; `(start ,@nl1 end) ;; => '(start (1 2 3) (4 5) end)
;; ; `(start ,nl1 .. end) => '(start (1 2 3) (4 5) end)
;; ; `(start ,nl1 .. .. end) => '(start 1 2 3 4 5 end)

;; `(start ,nl2 end) ;; => '(start (((1 2 3) (4 5)) ((6 7))) end)
;; `(start ,@nl2 end) ;; => '(start ((1 2 3) (4 5)) ((6 7)) end)
;; ; `(start ,nl2 .. end) ;; => '(start ((1 2 3) (4 5)) ((6 7)) end)
;; ; `(start ,nl2 .. .. end) ;; => '(start (1 2 3) (4 5) (6 7) end)
;; ; `(start ,nl2 .. .. .. end) ;; => '(start 1 2 3 4 5 6 7 end)


;; ;; (define-syntax (reconst stx)
;; ;;   (syntax-case stx ()
;; ;;     [(_ (quote (id ...)))
;; ;;      (with-syntax ([(temp ...) (generate-temporaries #'(id ...))])
;; ;;        #'(let-values ([(temp ...) (values id ...)])
;; ;;            (list temp ...)))]))

;; (define-syntax reconst
;;   (syntax-rules ()
;;     [(_ (quote ()))
;;      '()]
;;     [(_ (quote (a . d)))
;;      (let ([tmp 'a])
;;        (cons tmp (reconst (quote d))))]
;;     [(_ (quote const))
;;      'const]))

;; (define-syntax quasiwrap
;;   (syntax-rules (quasiquote quote unquote unquote-splicing ..)
;;     [(_ (quasiquote ())) `()]
;;     [(_ (quasiquote (unquote const))) `,const]
;;     [(_ (quasiquote (unquote-splicing const))) (flatten-n 1 `,const)]
;;     [(_ (quasiquote (a .. .. .. . d)))
;;      (let ([tmp (flatten-n 3 (quasiwrap (quasiquote a)))])
;;        (cons tmp (quasiwrap (quasiquote d))))]
;;     [(_ (quasiquote (a .. .. . d)))
;;      (let ([tmp (flatten-n 2 (quasiwrap (quasiquote a)))])
;;        (cons tmp (quasiwrap (quasiquote d))))]
;;     [(_ (quasiquote (a .. . d)))
;;      (let ([tmp (flatten-n 1 (quasiwrap (quasiquote a)))])
;;        (cons tmp (quasiwrap (quasiquote d))))]
;;     [(_ (quasiquote (a . d)))
;;      (let ([tmp (quasiwrap (quasiquote a))])
;;        (cons tmp (quasiwrap (quasiquote d))))]
;;     [(_ (quasiquote const)) (quasiquote const)]))

;; (define (flatten-n n ls)
;;   (let loop ([n n] [ls ls])
;;     (cond
;;       [(zero? n) ls]
;;       [else (loop (- n 1) (apply append ls))])))

;; (define (flatten-1 ls)
;;   (apply append ls))


;; tests

(define (add123 x)
  (values (+ 1 x)
          (+ 2 x)
          (+ 3 x)))

(define (always-foo x) 'foo)

;; basic functionality
(kmatch '(1 2 3)
  [`(,a ,b ,c) (guard (symbol? a)) a]
  [else 'oops])
;; => oops

;; CATA on itself
(kmatch '(1 2 3)
  [`(,[a] ,[b] ,[c]) (+ a b c)]
  [`,x (+ x x)])
;; => 12

;; CATA on an arbitrary function
(kmatch '(1 2 3)
  [`(,[always-foo -> a] ,b ,c) (guard (symbol? a)) a]
  [else 'oops])
;; => 'foo

;; CATA: multiple values
(kmatch '(1 2 3)
  [`(,[add123 -> a1 a2 a3] ,b ,c) `(,a1 ,a2 ,a3)]
  [else 'oops])
;; => '(2 3 4)

;; CATA: values/receivers length mismatch
(kmatch '(1 2 3)
  [`(,[add123 -> a1 a2] ,b ,c) `(,a1 ,a2)]
  [else 'oops])
;; => '(2 3)

;; CATA: values/receivers length mismatch
(kmatch '(0 1 2)
  [`(,[] ,[] ,[]) (values)]
  [`,x (if (> x 0)
           'cool
           (printf "warning: ~s <= 0\n" x))])
;; => warning: 0 <= 0
