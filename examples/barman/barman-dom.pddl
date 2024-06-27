(define 
    (domain Barman)
    (:requirements :typing :adl :quantified-preconditions :numeric-fluents :durative-actions :duration-inequalities :conditional-effects :time :derived-predicates)
    (:types 
        hand level container ingredient beverage location - object
        table dishwasher - location
        fluid solid - ingredient
        ice - solid
        bottle shaker serving_container - container
        shot glass - serving_container
    )
    (:predicates 
        (at-location ?c - container ?l - location)
        (in-use ?c - container)
        (active ?d - dishwasher)
        (chilled ?c - container ?i - fluid)
        (clean ?c - container)
        (served ?c - serving_container)
        (mixed ?f1 ?f2 - fluid ?c - container)
    )
    (:functions
        (solid-volume ?i - solid)- number
        (flow-rate ?from ?to - container)- number
        (volume ?c - container) - number
        (fluid-level ?c - container) - number
        (solid-level ?c - container) - number
        (level ?c - container ?i - ingredient) - number
        (demand ?b - beverage) - number
        (error-ratio) - number
        ; (holding ?h - hand) - container
    )

    (:derived (in-use1 ?c - container)
        (or
            (exists (?c1 - serving_container) (and (= ?c ?c1) (has_been_served ?c1)))
            (in-use ?c)
        )
    )

    (:action pick-up 
        :parameters (?c - container ?h - hand)
        :precondition (and 
            (not (exists (?c1 - container) (= (holding ?h) ?c1)))
            (not (in-use ?c))
            (exists (?l - location) (at-location ?c ?l))
        )
        :effect (and 
            (forall (?l - location) (not (at-location ?c ?l)))
            (assign (holding ?h) ?c)
        )
    )

    (:action put-down
        :parameters (?c - container ?l - location ?h - hand)
        :precondition (and 
            (not (in-use ?c))
            (= (holding ?h) ?c)
        )
        :effect (and 
            (at-location ?c ?l)
            (assign (holding ?h) undefined)
        )
    )
    

    (:derived (contains ?b - (either container beverage) ?i - ingredient)
        (> (level ?b ?i) 0)
    )

    (:derived (is-empty ?c - container)
        (not (exists ?i - ingredient)
            (contains ?c ?i)
        )
    )

    (:derived (is-cold ?c - container ?i - ingredient)
        (or
            (chilled ?c ?i)
            (exists (?ice - ice) (contains ?c ?ice))
        )
    )

    (:derived (is-empty ?c - container)
        (forall (?i - ingredient)
            (not (contains (?b ?i)))
        )
    )

    (:derived (ready-to-serve ?c - serving_container ?b - beverage)
        (and 
            (forall (?i - ingredient) 
                (imply
                    (contains ?b ?i) 
                    (and
                        (<= (- (level ?c ?i) (level ?b ?i)) error-ratio)
                        (<= (- (level ?b ?i) (level ?c ?i)) error-ratio)
                    )
                )
            )
            (forall (?i - ingredient) 
                (imply
                    (contains ?c ?i)
                    (contains ?b ?i)
                )
            )
        )
    )

    (:action serve 
        :parameters (?c - serving_container ?b - beverage ?h - hand)
        :precondition (and
            (ready-to-serve ?c ?b)
            (= (holding ?h) ?c)
            (not (in-use ?c))
        )
        :effect (and 
            (decrease (demand ?b) 1)
            (served ?c)
            (assign (holding ?h) undefined)
        )
    )

    (:durative-action pour
        :parameters (?from ?to - container ?h - hand)
        :duration (<= ?duration 10)
        :condition (and 
            (at start (and
                (exists (?i - ingredient) (contains ?from ?i))
                (not (in-use ?from))
                (not (in-use ?to))
                (not ?from ?to)
            ))
            (over all (and 
                (= (holding ?h) ?from)
                (<= (* (flow-rate ?from ?to) ?duration) (- (volume ?to) (+ (solid-level ?to) (fluid-level ?to))))
                (<= (* (flow-rate ?from ?to) ?duration) (fluid-level ?from))
            ))
        )
        :effect (and 
            (at start (and (in-use ?from) (in-use ?to)))
            (at end (and (not (in-use ?from)) (not (in-use ?to))))
            (at end (and
                (decrease (fluid-level ?from) (* ?duration (flow-rate ?from ?to)))
                (forall (?f - fluid) 
                    (when (at start (contains ?from ?i))
                        (and
                            (decrease (level ?from ?i) 
                                (* (/ (level ?from ?i) (fluid-level ?from)) (* ?duration (flow-rate ?from ?to))))
                            (increase (level ?to ?i)
                                (* (/ (level ?from ?i) (fluid-level ?from)) (* ?duration (flow-rate ?from ?to))))
                        )
                    ) 
                )
            ))
            (forall (?f - fluid)
                (and 
                    (when 
                        (at start (and 
                            (contains ?from ?f) 
                            (not (contains ?to ?f))
                            (chilled ?from ?f)
                        ))
                        (at end (chilled ?to ?f))
                    )
                    (when (at start (contains ?to ?f))
                        (at end (not (chilled ?to ?f)))
                    )
                )
            )
            (forall (?f - fluid) (and 
                  
            ))
            (at start 
                (not (clean ?c))
            )
        )
    )

    (:durative-action shake
        :parameters (?s - shaker ?g - glass ?h1 ?h2 - hand)
        :duration (and 
            (>= ?duration 5)
            (<= ?duration 10)
        )
        :condition (and
            (at start
                (is-empty ?s)
                (is-clean ?s)
            )
            (over all (and
                (holding ?s ?h1)
                (holding ?g ?h2)
            ))
        )
        :effect (and
            (at start (interacting ?from ?to))
            (at end (not (interacting ?from ?to)))
            (when (at start (exists (?ice - ice) (contains ?g ?ice)))
                (at end (forall (?f - fluid) 
                    (when (contains ?c ?f)
                        (chilled ?c ?f)
                    )
                ))
            )
            (at end (forall ?f1 ?f2 - fluid)
                (when (and (contains ?c ?f1) (contains ?c ?f2))
                    (mixed ?f1 ?f2 ?c)
                )
            )
        )
    )

    (:durative-action wash-dishes
        :parameters (?dishwasher - dishwasher)
        :duration (= ?duration 60)
        :condition (and 
            (at start (and
                
            ))
            (over all (and

            ))
            (at end (and

            ))
        )
        :effect (and 
            (at start (and
                (forall (?c - container) 
                    (when (at-location ?c ?dishwasher)
                        (in-use ?c)
                    )
                )
            ))
            (at end (and
                (forall (?c - container) 
                    (when (at-location ?c ?dishwasher)
                        (not (in-use ?c))
                    )
                )
            ))
        )
    ) 
    
    
)