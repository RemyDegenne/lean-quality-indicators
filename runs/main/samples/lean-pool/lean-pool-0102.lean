public section

open Filter Function MeasureTheory Set

open scoped Convolution Topology

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

local instance :
    Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

theorem tendsto_toLp_mul_left_of_nnnorm_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {φ : X → ℝ}
    {f : ℕ → X → ℝ} {g : X → ℝ} {C : NNReal}
    (hφ : AEStronglyMeasurable φ μ) (hC : ∀ x, ‖φ x‖₊ ≤ C)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto
      (fun n => (memLp_mul_left_of_nnnorm_bound hφ (hf n)
        (Filter.Eventually.of_forall hC)).toLp (fun x => φ x * f n x))
      atTop
      (𝓝 ((memLp_mul_left_of_nnnorm_bound hφ hg
        (Filter.Eventually.of_forall hC)).toLp (fun x => φ x * g x))) := by
  let hmul (n : ℕ) : MemLp (fun x => φ x * f n x) 2 μ :=
    memLp_mul_left_of_nnnorm_bound hφ (hf n) (Filter.Eventually.of_forall hC)
  let hmulG : MemLp (fun x => φ x * g x) 2 μ :=
    memLp_mul_left_of_nnnorm_bound hφ hg (Filter.Eventually.of_forall hC)
  have hprodBound (n : ℕ) :
      eLpNorm (fun x => φ x * (f n x - g x)) 2 μ ≤
        (C : ENNReal) * eLpNorm (f n - g) 2 μ := by
    have h := eLpNorm_mul_left_le_of_nnnorm_bound hφ
      ((hf n).sub hg).aestronglyMeasurable
      (Filter.Eventually.of_forall hC) 2
    simpa [ENNReal.smul_def] using h
  have hprodLimit : Tendsto
      (fun n => eLpNorm (fun x => φ x * (f n x - g x)) 2 μ) atTop (𝓝 0) := by
    have hscaled : Tendsto
        (fun n => (C : ENNReal) * eLpNorm (f n - g) 2 μ) atTop (𝓝 0) := by
      convert ((ENNReal.continuous_mul_const (a := (C : ENNReal))
        ENNReal.coe_ne_top).continuousAt.tendsto.comp hconv) using 1
      · funext n
        simp [mul_comm]
      · simp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hscaled
    · filter_upwards [] with n
      exact (bot_le : (0 : ENNReal) ≤ eLpNorm (fun x => φ x * (f n x - g x)) 2 μ)
    · filter_upwards [] with n
      exact hprodBound n
  have hprodLimit' : Tendsto
      (fun n => eLpNorm ((fun x => φ x * f n x) - (fun x => φ x * g x)) 2 μ)
      atTop (𝓝 0) := by
    refine hprodLimit.congr' ?_
    filter_upwards [] with n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    ring
  have hreal : Tendsto
      (fun n => (eLpNorm ((fun x => φ x * f n x) - (fun x => φ x * g x)) 2 μ).toReal)
      atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => ((hmul n).sub hmulG).eLpNorm_ne_top)).2 hprodLimit'
  have hdist : Tendsto
      (fun n => dist ((hmul n).toLp (fun x => φ x * f n x))
        (hmulG.toLp (fun x => φ x * g x))) atTop (𝓝 0) := by
    refine hreal.congr' ?_
    filter_upwards [] with n
    rw [Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [(hmul n).coeFn_toLp, hmulG.coeFn_toLp] with x hx hy
    change φ x * f n x - φ x * g x =
      (hmul n).toLp (fun x => φ x * f n x) x -
        hmulG.toLp (fun x => φ x * g x) x
    exact congrArg₂ (fun a b : ℝ => a - b) hx.symm hy.symm
  exact (tendsto_iff_dist_tendsto_zero).2 hdist

end CKN
end
end
