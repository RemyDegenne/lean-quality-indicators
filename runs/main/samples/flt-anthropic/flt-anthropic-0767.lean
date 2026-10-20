namespace P2MW.S_CerednikDrinfeld_Omega_exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube

set_option autoImplicit false

p2m_open

noncomputable section

namespace CerednikDrinfeld

namespace Omega

namespace AnnulusUnits

p2m_open

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

variable (ϖ : PseudoUniformizer K₀ K)

local notation "𝔯" => Valued.v (algebraMap K₀ K (PseudoUniformizer.ϖ ϖ))

theorem exists_v_eval_eq [IsAlgClosed K]
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 𝔯 ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (p : K[X]) (hp : ∀ z ∈ stdEdgeTube ϖ, p.eval z ≠ 0) :
    ∃ (c : Γ₀) (m : ℕ), ∀ z ∈ stdEdgeTube ϖ, Valued.v (p.eval z) = c * Valued.v z ^ m := by
  by_cases hp0 : p = 0
  ·
    refine ⟨1, 0, fun z hz => ?_⟩
    exact absurd (by rw [hp0, eval_zero]) (hp z hz)
  have hroots : ∀ α ∈ p.roots, α ∉ stdEdgeTube ϖ := fun α hα hmem => hp α hmem ((mem_roots hp0).1 hα)
  obtain ⟨c, m, h⟩ := exists_v_multiset_prod_sub_eq ϖ hunif p.roots hroots
  refine ⟨Valued.v p.leadingCoeff * c, m, fun z hz => ?_⟩
  have hsplit := (IsAlgClosed.splits p).eq_prod_roots
  conv_lhs => rw [hsplit]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, map_mul]
  have : (Multiset.map (eval z ∘ fun x => X - C x) p.roots) = Multiset.map (fun α => z - α) p.roots := by
    refine Multiset.map_congr rfl fun α _ => ?_
    simp
  rw [this, h z hz, mul_assoc]

end AnnulusUnits
end Omega
end CerednikDrinfeld
end
end P2MW.S_CerednikDrinfeld_Omega_exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube
