namespace OAI

noncomputable section

open Set Filter MeasureTheory

open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise

namespace HarmonicCounterexample.Main.SmoothMetric3

lemma smooth_smul_memLp {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcompact : HasCompactSupport φ) (v : E3) :
    MemLp (fun x ↦ φ x • v) 2 (volume : Measure E3) :=
  (hφ.continuous.smul continuous_const).memLp_of_hasCompactSupport
    (hcompact.smul_right)

end HarmonicCounterexample.Main.SmoothMetric3
end
end OAI
