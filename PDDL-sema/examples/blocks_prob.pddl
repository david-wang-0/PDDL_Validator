(define (problem BlocksProb)
(:domain BlocksDom)
(:requirements :quantified-preconditions)

(:objects A B C)
(:INIT (ONTABLE A) (ON C B) (ON B A) (HANDEMPTY))
(:goal (forall (?block) (ONTABLE ?block)))
)