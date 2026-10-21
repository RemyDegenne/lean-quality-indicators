namespace OAI

section

section

open Set Filter MeasureTheory

open scoped Topology ENNReal NNReal

open Filter Set

open scoped Topology NNReal

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal

open MeasureTheory Filter Set Metric

open scoped Topology Pointwise NNReal

open Set MeasureTheory

open scoped RealInnerProductSpace

open Matrix

open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings

open Matrix

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma metricTotalRadialForm_posSemidef
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ)
    (hG : G.PosSemidef) (hα : ∀ v : ι → ℝ, (α ⬝ᵥ v)^2 ≤ v ⬝ᵥ G.mulVec v) :
    (metricTotalRadialForm G g r t α γ).PosSemidef := by
  have hQ : (G-vecMulVec α α).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.IsHermitian.sub hG.isHermitian
      simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star α).isHermitian
    · intro v
      simp only [star_trivial]
      rw [Matrix.sub_mulVec,dotProduct_sub,dotProduct_vecMulVec_self]
      exact sub_nonneg.mpr (hα v)
  exact totalRankOneForm_posSemidef _ _ _ (hQ.smul (sq_nonneg _))

end CAT0Fillings
end
end
end OAI
