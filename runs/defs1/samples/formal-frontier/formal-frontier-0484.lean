@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe uR uC uD uE uM uN uP uι uκ uI

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

section Coordinates

variable (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)

variable {ι : Type uι} [Finite ι]

/-- Algebraic finite-basis tensor coordinates, using Mathlib's tensor and Finsupp APIs. -/
noncomputable def tensorCoordinateLinearEquiv (b : Module.Basis ι R C) :
    TensorProduct R C M ≃ₗ[R] (ι → M) := by
  classical
  exact (TensorProduct.equivFinsuppOfBasisLeft b).trans
    (Finsupp.linearEquivFunOnFinite R M ι)

end Coordinates
end TopModuleCat
end
