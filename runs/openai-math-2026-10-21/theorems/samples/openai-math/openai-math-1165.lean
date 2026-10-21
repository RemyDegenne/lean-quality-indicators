namespace OAI

section

section

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal Topology RealInnerProductSpace Convolution

open Laplacian

namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

theorem laplacian_compact_convolution {f k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) (x : X) :
    Δ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] Δ k) x := by
  have hc := hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hk
  rw [laplacian_eq_sum_directional hc, convolution_mul]
  simp_rw [laplacian_eq_sum_directional hk, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    let v := (stdOrthonormalBasis ℝ X) i
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ k y v) :=
      (hk.fderiv_right (by simp)).clm_apply contDiff_const
    have he : (fun y ↦ fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) y v) =
        f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (fun y ↦ fderiv ℝ k y v) :=
      funext (fun y ↦ fderiv_compact_convolution hf hk hs y v)
    change fderiv ℝ (fun y ↦ fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) y v) x v = _
    rw [he, fderiv_compact_convolution hf hd (hs.fderiv_apply ℝ v)]
    rfl
  · intro i _
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ k y ((stdOrthonormalBasis ℝ X) i)) :=
      (hk.fderiv_right (by simp)).clm_apply contDiff_const
    exact ((hs.fderiv_apply ℝ _).fderiv_apply ℝ _).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) hf
      ((hd.continuous_fderiv (by simp)).clm_apply continuous_const) x

end CubicTorus
end
end
end
end OAI
