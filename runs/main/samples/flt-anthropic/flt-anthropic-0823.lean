namespace P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open scoped MatrixGroups

p2m_open

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section E3sec

p2m_open

namespace FTW

variable {G : Type} [Group G] {W : Type} [MulAction G W] {𝒯 : SimpleGraph W} [GraphAction G 𝒯]

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Star

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

variable (hfin : ∀ w : W, Finite (MulAction.stabilizer G w))

variable (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)

variable [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotVert G W)] {E : Type} [Fintype E]

variable (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})

theorem card_filter_smul_eq' {H : Subgroup G} [Fintype H] {X : Type} [MulAction G X] [DecidableEq X]
    (x : X) (h₀ : H) :
    (Finset.univ.filter fun h : H => (h : G) • x = (h₀ : G) • x).card = Fintype.card {s : H // (s : G) • x = x} := by
  classical
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun h => ⟨h₀⁻¹ * h.1, ?_⟩
      invFun := fun s => ⟨h₀ * s.1, ?_⟩
      left_inv := fun h => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp) }
  · show ((h₀⁻¹ * h.1 : H) : G) • x = x
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h.2, inv_smul_smul]
  · show ((h₀ * s.1 : H) : G) • x = (h₀ : G) • x
    rw [Subgroup.coe_mul, mul_smul, s.2]

end Star
end FTW
end E3sec
end
end P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq
