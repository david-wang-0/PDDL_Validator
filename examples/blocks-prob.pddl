(define (problem blocks-prob)
(:domain blocks-dom)
(:requirements :quantified-preconditions)

(:objects A B C)
(:INIT (CLEAR C) (ONTABLE A) (ON C B) (ON B A)(HANDEMPTY))
(:goal (forall (?block)))
)