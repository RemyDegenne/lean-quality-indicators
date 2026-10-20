public section

namespace TauCeti

open MeasureTheory Polynomial ProbabilityTheory

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

@[simp]
theorem gaussianHermitePiBasis_repr_L2piMul
    (F : ι → Lp 𝕜 2 (gaussianReal 0 1)) (a : ι → ℕ) :
    (gaussianHermitePiBasis 𝕜 ι).repr (L2piMul F) a
      = ∏ i, ∫ x : ℝ, (algebraMap ℝ 𝕜)
          (aeval x (hermite (a i)) / Real.sqrt ((a i).factorial : ℝ)) * F i x
            ∂(gaussianReal 0 1) := by
  rw [HilbertBasis.repr_apply_apply, gaussianHermitePiBasis_apply]
  calc
    inner 𝕜 (L2piMul fun i => gaussianHermiteHilbertBasis 𝕜 (a i)) (L2piMul F)
        = ∏ i, (gaussianHermiteHilbertBasis 𝕜).repr (F i) (a i) := by
          simpa only [HilbertBasis.repr_apply_apply, piHilbertBasis_apply] using
            piHilbertBasis_repr_L2piMul (fun _ : ι => gaussianHermiteHilbertBasis 𝕜) F a
    _ = _ := Finset.prod_congr rfl fun i _ => by
      rw [gaussianHermiteHilbertBasis_repr_apply]

end TauCeti
end
