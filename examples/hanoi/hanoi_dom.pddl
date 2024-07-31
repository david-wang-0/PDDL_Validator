(define (domain hanoi)
(:requirements :adl :types)
(:predicates (clear ?x)
             (on ?x ?y)
             (smaller ?x ?y))

(:functions
    (under ?x) - object
)

(:action move
:parameters (?disc ?from ?to)
:precondition (and (smaller ?to ?disc) 
                   (on ?disc ?from) 
                   (clear ?disc) 
                   (clear ?to))
:effect  (and (clear ?from) 
              (on ?disc ?to) 
              (not (on ?disc ?from))  
              (not (clear ?to)))
 )) 