(define (domain RechargingRobotsDom)
(:requirements :negative-preconditions :quantified-preconditions :typing :adl :numeric-fluents :object-fluents)

(:types
    location - object
    robot - object
    config - object
)

(:predicates
    ;; Two locations are connected in the graph of locations
    (CONNECTED ?l1 - location ?l2 - location)
    ;; Definition of a guarding configuration, i.e., one atom per location
    ;; in each configuration
    (GUARD-CONFIG ?c - config ?l - location)
    ;; Robot stopped and is guarding all locations connected to the
    ;; location where robot is located
    (stopped ?r - robot)
    ;; Location ?l is guarded by at least one robot
    (guarded ?l - location)
    ;; Configuration is fullfilled, i.e., all of its locations were guarded
    ;; at some point.
    (config-fullfilled ?c - config)
)

(:functions
    (battery-level ?r - robot) - number
    (loc ?r - robot) - location
    move-cost - number
    recharge-cost - number
)

;; Move the robot ?r from the location ?from to the location ?to while
;; consuming the battery -- it is decreased by one from ?fpre to ?fpost
(:action move
    :parameters (?r - robot ?to - location)
    :precondition
        (and
            (not (stopped ?r))
            (or (CONNECTED (loc ?r) ?to) (CONNECTED ?to (loc ?r)))
            (> (battery-level ?r) 0)
        )
    :effect
        (and
            (assign (at ?r) ?to)
            (decrease (battery-level ?r) move-cost)
            (increase total-cost move-cost)
        )
)

;; Recharge robot ?rto at location ?loc by transfering one unit of battery
;; charge from the robot ?rfrom
(:action recharge
    :parameters (?rfrom - robot ?rto - robot)
    :precondition
        (and
            (not (= ?rfrom ?rto))
            (= (at ?rfrom) (at ?rto))
            (> (battery-level ?rfrom) 0)
        )
    :effect
        (and
            (increase (battery ?rfrom) 1)
            (assign (battery ?rto) ((battery ?rto) - 1))
            (increase total-cost recharge-cost)
        )
)

;; Stop the robot at its current location and guard the neighborhood.
;; Once the robot stopped it can move again only when the configuration is
;; fullfilled, i.e., stopping too early can result in a dead-end.
;; Note that the conditional effect can be compiled away without blow-up,
;; because it is conditioned on a static predicates.
(:action stop-and-guard
    :parameters (?r - robot)
    :precondition
        (not (stopped ?r))
    :effect
        (and
            (stopped ?r)
            (guarded (loc ?r))
            (forall (?l2 - location)
                (when (or (CONNECTED ?l ?l2) (CONNECTED ?l2 ?l))
                      (guarded ?l2)
                )
            )
        )
)

;; Verify that the given configuration is fullfilled, i.e., robots guard
;; all locations from the configuration.
;; Note that this action unblocks all robots whether they participate in
;; guarding of the configuration or not. This simplifies the model because
;; otherwise, we would need to keep track of what location is guarded by
;; which robot (it can be guarded by multiple ones).
;; Also note the precondition does not have to inccur exponential blow-up
;; because the imply condition is conditioned on a static predicate.
(:action verify-guard-config
    :parameters (?c - config)
    :precondition
        (and
            (forall (?l - location)
                (imply (GUARD-CONFIG ?c ?l) (guarded ?l))
            )
        )
    :effect
        (and
            (forall (?r - robot) 
                (when 
                    (exists (?l - location) 
                        (and 
                            (GUARD-CONFIG ?c ?l) 
                            (= (loc ?r) ?l)
                        ))
                    (and 
                        (not (stopped ?r)) 
                        (not (guarded (loc ?r))))
                )
            (config-fullfilled ?c)
        )
    )
)
)