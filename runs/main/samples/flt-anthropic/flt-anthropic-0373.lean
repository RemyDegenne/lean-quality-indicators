namespace P2MW.S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial

open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

p2m_open

namespace QExpN

section Slots

variable {K : Type} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
  (hζ : IsPrimitiveRoot (ζ : K) ℓ)

omit hℓ in
@[scoped simp] lemma liftPerm_zero (e : Equiv.Perm (Fin ℓ)) : liftPerm ℓ e 0 = 0 :=
  Equiv.Perm.decomposeFin_symm_apply_zero 0 e

end Slots
end QExpN
end ModularCurve
end
end P2MW.S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant
