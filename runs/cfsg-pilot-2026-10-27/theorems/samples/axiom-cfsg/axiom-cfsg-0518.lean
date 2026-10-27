public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PrimeCubeDivisorCoherence

open TypeVTwoFamilyJoining NormalLinearInduced

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [K.Normal] [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]

namespace IsPrimeCubeDivisorHyp

variable {h : IsPrimeCyclicTIHyp K W₁ W₂} {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ζ : ↥L → ℂ} {p d n : ℕ} {δ : ℤ} {A₀ : Set G} {T : G → Subgroup G}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  (hC : IsPrimeCubeDivisorHyp h σ ζ p d n δ A₀ T ω)

include hC

omit [K.Normal] in
theorem eight_le_ncard : 8 ≤ (indFamLinear K).ncard := by
  have := Fintype.ofFinite ↑(Irr ↥W₁)
  have := Fintype.ofFinite ↑(Irr ↥W₂)
  have hcount := hC.arrayHyp.ncard_indFamLinear_mul
  have h1 := hC.prime_add_one_eq
  have h3 : 3 ≤ Nat.card ↥W₁ := h.isCyclicTIPair.three_le_natCard_left
  have hkey : 8 * Nat.card ↥W₁ ≤ p ^ 2 - 1 := by
    have hsq : 8 * Nat.card ↥W₁ + 1 ≤ p ^ 2 := by nlinarith
    omega
  rw [← hcount] at hkey
  exact Nat.le_of_mul_le_mul_right hkey Nat.card_pos

end IsPrimeCubeDivisorHyp
end PrimeCubeDivisorCoherence
end CFSG.FeitThompson
end
