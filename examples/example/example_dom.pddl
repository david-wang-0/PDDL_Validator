(define 
    (domain Example)
    (:requirements :object-fluents)

   
    (:predicates
        (p)
        (q ?obj)
    )

    (:functions
        (f ?obj) - object
    )

    (:action do
        :parameters (?obj)
        :precondition (= (f ?obj) (f ?obj))
        :effect (p)
    )

    (:action do1
        :parameters (?obj)
        :effect (q (f ?obj))
    )
)