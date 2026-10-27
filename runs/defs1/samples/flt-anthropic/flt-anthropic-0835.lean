set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IntermediateField IsDedekindDomain

open Topology TopCat

universe u

namespace AlgebraicCurve

namespace CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)

open IsLocalRing

open TopologicalSpace

section LocalSections

variable (a : K)

def σ₁ : Γ(X₀ K t, U₁ K t a) := (((isUnit_res_tma K t a).unit⁻¹ : (Γ(X₀ K t, U₁ K t a))ˣ) : _)

end LocalSections
end CurveModel
end AlgebraicCurve
end
