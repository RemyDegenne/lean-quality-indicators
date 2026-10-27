public section

open Polynomial WeierstrassCurve.Affine

namespace TauCeti

open scoped Polynomial.Bivariate

variable {F : Type*} [Field F]

namespace Isogeny

variable {W₁ W₂ : WeierstrassCurve.Affine F}

/-- The function-field pullback induced by an isogeny. It is the unique extension of the
coordinate pullback across the target fraction field. -/
noncomputable def fieldPullback (φ : Isogeny W₁ W₂) :
    W₂.FunctionField →ₐ[F] W₁.FunctionField :=
  IsFractionRing.liftAlgHom φ.pullback_injective

end Isogeny
end TauCeti
end
