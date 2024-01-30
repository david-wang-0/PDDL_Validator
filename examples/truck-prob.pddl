




(define (problem TruckProb)
(:domain TruckDom)
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

(:goal (and 
	(delivered package1 l3)
	(at-destination package2 l1)
	(delivered package3 l1)))
)