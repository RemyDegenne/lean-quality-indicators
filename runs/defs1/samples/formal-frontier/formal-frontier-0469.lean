set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

/-- The principal-cocycle map as a continuous linear map.
Its underlying linear map reduces to `principalToCrossed`. -/
@[expose]
def principalToCrossedL [TopRep.JointlyContinuous X] :
    X →L[k] continuousCrossedHom X where
  __ := principalToCrossed X
  cont := continuous_induced_rng.2 <|
    (orbitMap X).continuous.sub ContinuousMap.continuous_const'

end ContinuousCohomology
end
