set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IntermediateField IsDedekindDomain

open Topology TopCat

universe u

namespace AlgebraicCurve

namespace CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)

section Charts

@[simp] theorem coe_tInvChart : (tInvChart K t : L) = t⁻¹ := rfl

end Charts
end CurveModel
end AlgebraicCurve
end
