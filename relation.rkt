#lang rosette

(require "evaluator.rkt" "table.rkt")

(provide (all-defined-out))

(define-namespace-anchor anc)
(define ns (namespace-anchor->namespace anc))

;; q-scan : Nat -> Query S
(struct q-scan (id) #:transparent)
;; q-values : Nat -> List (List Expr) -> Query S
(struct q-values (schema data) #:transparent)
;; q-filter : Expr -> Query S -> Query S
(struct q-filter (condition source) #:transparent)
;; q-project : List Expr -> Query S' -> Query S
(struct q-project (targets source) #:transparent)
;; q-join : JoinKind -> Expr -> Query S' -> Query S'' -> Query (S ++ S'')
(struct q-join (kind condition left right) #:transparent)
;; q-union : Query S -> Query S -> Query S
(struct q-union (left right) #:transparent)
;; q-union : Query S -> Query S
(struct q-distinct (source) #:transparent)
(struct q-agg (aggs group-set source) #:transparent)
(struct v-agg (name cols) #:transparent)

;; v-var : Nat -> Expr
(struct v-var (id) #:transparent)
;; v-op : String -> List Expr -> Expr
(struct v-op (name args) #:transparent)
;; v-hop : String -> List Expr -> Query S -> Expr
(struct v-hop (name args query) #:transparent)

;; denote-q : Query S -> List Table -> (List Any -> List S)
(define (denote-q query tables)
  (match query
    [(q-scan id)
     (let ([t (list-ref tables id)])
       (list (lambda (env) (get-content t)) (length (get-schema t))))]
    [(q-values schema data)
     (list (lambda (env) (map (lambda (row) (cons row 1)) data)) schema)]
    [(q-filter condition source)
     (match-let ([(list source schema) (denote-q source tables)])
       (list
        (lambda (env)
          (let ([condition (denote-v condition tables)])
            (map (match-lambda
                   [(cons t n) (cons t (if (condition (append env t)) n 0))])
                 (source env))))
        schema))]
    [(q-project targets source)
     (list
      (lambda (env)
        (map (match-lambda
               [(cons t n)
                (cons (map (lambda (target) ((denote-v target tables) (append env t))) targets) n)])
             ((car (denote-q source tables)) env)))
      (length targets))]
    [(q-join kind condition left right)
     (match-let ([(list left l-schema) (denote-q left tables)]
                 [(list right r-schema) (denote-q right tables)])
       (list
        (lambda (env)
          (let* ([left (left env)]
                 [right (right env)]
                 [product (xproduct-raw left right)]
                 [condition (denote-v condition tables)]
                 [joined (map (match-lambda
                                [(cons t n) (cons t (if (condition (append env t)) n 0))])
                              product)])
            (match kind
              ['inner joined]
              ['left (append joined
                             (outer-join-null-rows #t left right joined l-schema r-schema))]
              ['right (append joined
                              (outer-join-null-rows #f left right joined l-schema r-schema))]
              ['full (append joined
                             (outer-join-null-rows #t left right joined l-schema r-schema)
                             (outer-join-null-rows #f left right joined l-schema r-schema))])))
        (+ l-schema r-schema)))]
    [(q-union left right)
     (match-let ([(list left l-schema) (denote-q left tables)]
                  [(list right r-schema) (denote-q right tables)])
       (if (equal? l-schema r-schema)
           (list
            (lambda (env)
              (append (left env) (right env)))
            l-schema)
           (error "unmatched schema")))]
    [(q-distinct source)
     (match-let ([(list source schema) (denote-q source tables)])
       (list
        (lambda (env) (dedup (source env)))
        schema))]
    [(q-agg aggs group-set source)
     (match-let ([(list source schema) (denote-q source tables)])
       (list
        (lambda (env)
          (map (match-lambda
                 [(cons (cons group keys) n)
                  (cons
                   (append keys
                          (map (match-lambda
                                 [(v-agg name cols)
                                  (apply (eval name ns) (project-list cols group))])
                               aggs))
                   n)])
               (group-by-helper (source env) group-set)))
        (+ (length group-set) (length aggs))))]))

;; denote-v : Expr -> List Table -> (List Any -> Any)
(define (denote-v expr tables)
  (match expr
    [(v-var id) (lambda (env) (list-ref env id))]
    [(v-op (or (? number? v) (? string? v) (? boolean? v)) '()) (lambda (env) v)]
    [(v-op name args)
     (lambda (env)
       (apply (eval name ns)
              (map (lambda (arg) ((denote-v arg tables) env)) args)))]
    [(v-hop 'exists '() query)
     (lambda (env) (not (table-content-empty? ((car (denote-q query tables)) env))))]
    [(v-hop 'unique '() query)
     (lambda (env) (table-content-distinct? ((car (denote-q query tables)) env)))]
    [(v-hop 'in row query)
     (lambda (env)
       (let ([row (map (lambda (val) ((denote-v val tables) env)) row)]
             [query ((car (denote-q query tables)) env)])
         (in-table-content? row query)))]))
