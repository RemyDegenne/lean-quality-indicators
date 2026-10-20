namespace P2MW.S_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

universe u v

namespace PRIMCOUNT

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]

local notation "ε" => Coalgebra.counit (R := k) (A := A)

variable {k A}

variable (k A)

theorem toCotDual_toCotangent {φ : CartierDual k A} (hφ : φ ∈ primitives k (CartierDual k A)) (x : ↥(I k A)) :
    toCotDual k A hφ ((I k A).toCotangent x) = φ x := by
  change ((((I k A) • ⊤ : Submodule A ↥(I k A)).restrictScalars k).liftQ (restrictI k A φ) (restrictI_vanishes k A hφ))
    ((Submodule.Quotient.restrictScalarsEquiv k ((I k A) • ⊤ : Submodule A ↥(I k A))).symm (Submodule.Quotient.mk x)) = φ x
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]
  rfl

end PRIMCOUNT
end P2MW.S_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace
