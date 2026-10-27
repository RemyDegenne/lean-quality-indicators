noncomputable section

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

variable (S : Type*) [CommRing S] [Algebra R S]

open TensorProduct

namespace ExteriorAlgebra

/-- The forward map of `ExteriorAlgebra.baseChangeEquiv`, lift from universal property of
tensor product and `ExteriorAlgebra`. -/
def baseChangeEquivForward : S ⊗[R] ExteriorAlgebra R M →ₐ[S] ExteriorAlgebra S (S ⊗[R] M) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (baseChangeEquivForwardAux R M S) (fun s y ↦ by
    simp [Algebra.commute_algebraMap_left])

end ExteriorAlgebra
end
