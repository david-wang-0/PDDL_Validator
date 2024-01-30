(define (domain TruckDom) 
(:requirements :typing)  

(:types location locatable - object
        truck package - locatable) 

(:predicates (at ?x - locatable ?l - location) 	     
             (in ?p - package ?t - truck) 	     
             (connected ?x ?y - location)
             (free ?t - truck)
 	     (delivered ?p - package ?l - location)
	     (at-destination ?p - package ?l - location)
)

(:action load
 :parameters (?p - package ?t - truck ?l - location)
 :precondition (and (at ?t ?l) (at ?p ?l) (free ?t))
 :effect (and (not (at ?p ?l)) (not (free ?t)) (in ?p ?t))
)

(:action unload
 :parameters (?p - package ?t - truck ?l - location)
 :precondition (and (at ?t ?l) (in ?p ?t))
 :effect (and (not (in ?p ?t)) (free ?t) (at ?p ?l))
 )

(:action drive
 :parameters (?t - truck ?from ?to - location)
 :precondition (and (at ?t ?from) (connected ?from ?to))
 :effect (and (not (at ?t ?from)) (at ?t ?to)))

(:action deliver
 :parameters (?p - package ?l - location )
 :precondition (and (at ?p ?l))
 :effect (and (not (at ?p ?l)) (delivered ?p ?l) (at-destination ?p ?l)))
) 