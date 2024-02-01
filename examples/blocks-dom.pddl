;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 4 Op-blocks world
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (domain BlocksDom)
  (:requirements :strips :negative-preconditions :equality :disjunctive-preconditions)
  (:predicates (on ?x ?y)
	       (ontable ?x)
	       (handempty)
	       (holding ?x)
         )

  (:action pick-up
	     :parameters (?x)
	     :precondition (and (forall (?z) (not (on ?z ?x))) (ontable ?x) (handempty))
	     :effect
	     (and (not (ontable ?x))
		   (not (handempty))
		   (holding ?x)))

  (:action put-down
	     :parameters (?x)
	     :precondition (holding ?x)
	     :effect
	     (and (not (holding ?x))
		   (handempty)
		   (ontable ?x)))

  (:action stack
	     :parameters (?x ?y)
	     :precondition (and (holding ?x) (forall (?z ?a) (or (not (= ?a ?y)) (not (on ?z ?a)))))
	     :effect
	     (and (not (holding ?x))
		   (handempty)
		   (on ?x ?y)))

  (:action unstack
	     :parameters (?x ?y)
	     :precondition (and (on ?x ?y) (not (exists (?z) (on ?z ?x))) (handempty))
	     :effect
	     (and (holding ?x)
		   (not (handempty))
		   (not (on ?x ?y))))
)

