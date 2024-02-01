(define (problem TruckProb)
(:domain TruckDom)
(:requirements :universal-preconditions :disjunctive-preconditions)
(:objects
	truck1 - truck
	package1 - package
	package2 - package
	package3 - package
	l1 - location
	l2 - location
	l3 - location)

(:init
	(at truck1 l3)
	(free truck1)
	(at package1 l2)
	(at package2 l2)
	(at package3 l2)
	(connected l1 l2)
	(connected l1 l3)
	(connected l2 l1)
	(connected l2 l3)
	(connected l3 l1)
	(connected l3 l2)
)

(:goal (forall (?loc - locatable ?p - package) (or (at ?loc l1) (at-destination ?p l1))))
)