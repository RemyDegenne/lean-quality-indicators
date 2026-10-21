namespace OAI

noncomputable section

open Set MeasureTheory Filter Function InnerProductSpace

open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical

open MeasureTheory Function

open Set Filter

open Set MeasureTheory Filter Function

open Set MeasureTheory Filter Function InnerProductSpace

open TopologicalSpace

open scoped CompactlySupported

open scoped ENNReal

open scoped Manifold

open scoped Topology CompactlySupported ComplexConjugate

open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical

open scoped Topology ENNReal NNReal

namespace Brennan

attribute [local irreducible] classWeight

attribute [local irreducible] classFun

attribute [local irreducible] rerootClass

lemma positiveResolvent_mul.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (h : ∀ n : ℕ, 1 ≤ ‖L^n‖)
    {τ : ℝ} (hτ : growthRate L h < τ) :
    positiveResolvent L τ * L = τ • (positiveResolvent L τ-1) ∧
    L * positiveResolvent L τ = τ • (positiveResolvent L τ-1) := by
  have ht : τ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le))
  have hs := summable_scaled_pow L h hτ
  have htail : ∑' n : ℕ, (τ⁻¹)^(n+1) • L^(n+1) = positiveResolvent L τ-1 := by
    have he := hs.sum_add_tsum_nat_add 1
    simpa [positiveResolvent] using eq_sub_iff_add_eq.mpr (by simpa [add_comm] using he)
  have he (n : ℕ) : τ • ((τ⁻¹)^(n+1) • L^(n+1)) = (τ⁻¹)^n • (L^n*L) := by
    rw [smul_smul,pow_succ,pow_succ]
    congr 1
    field_simp
  constructor
  · change (∑' n : ℕ, (τ⁻¹)^n • L^n)*L = _
    rw [show (∑' n : ℕ, (τ⁻¹)^n • L^n)*L =
      ∑' n : ℕ, ((τ⁻¹)^n • L^n)*L from
      ((ContinuousLinearMap.compL ℝ C(X,ℝ) C(X,ℝ) C(X,ℝ)).flip L).map_tsum hs,
      ← htail,← tsum_const_smul'']
    exact tsum_congr (fun n => by
      rw [he]; change ((τ⁻¹)^n • L^n).comp L = (τ⁻¹)^n • ((L^n).comp L)
      exact ContinuousLinearMap.smul_comp _ _ _)
  · change L*(∑' n : ℕ, (τ⁻¹)^n • L^n) = _
    rw [show L*(∑' n : ℕ, (τ⁻¹)^n • L^n) =
      ∑' n : ℕ, L*((τ⁻¹)^n • L^n) from
      ((ContinuousLinearMap.compL ℝ C(X,ℝ) C(X,ℝ) C(X,ℝ)) L).map_tsum hs,
      ← htail,← tsum_const_smul'']
    apply tsum_congr
    intro n
    rw [he]
    change L.comp ((τ⁻¹)^n • L^n) = (τ⁻¹)^n • ((L^n).comp L)
    rw [ContinuousLinearMap.comp_smul]
    congr 1
    change L * L^n = L^n * L
    rw [← pow_succ',← pow_succ]

end Brennan
end
end OAI
