@[expose] public section

open Module Polynomial

noncomputable section

universe u v

section Ring

variable {R : Type u} {S : Type v} [CommRing R] [Ring S] {f : R[X]} [Algebra R S]

namespace IsAdjoinRoot

variable (h : IsAdjoinRoot S f)

section Equiv

variable {T : Type*} [Ring T] [Algebra R T]

/-- Algebra isomorphism with `R[X]/(f)`. -/
def adjoinRootAlgEquiv : AdjoinRoot f ≃ₐ[R] S :=
  (Ideal.quotientEquivAlgOfEq R h.ker_map.symm).trans <|
    Ideal.quotientKerAlgEquivOfSurjective h.map_surjective

end Equiv
end IsAdjoinRoot
end Ring
end
end
