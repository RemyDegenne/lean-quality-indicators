namespace OAI

noncomputable section

open MeasureTheory Filter Topology

open scoped RealInnerProductSpace

namespace EuclideanFiveColor

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma weak_limit_nonneg {f : ℕ → RealL2 μ} {b : RealL2 μ}
    (ht : ∀ v, Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hf : ∀ n, 0 ≤ᵐ[μ] f n) : 0 ≤ᵐ[μ] b := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (MemLp.integrable (by norm_num) (Lp.memLp b))
  intro s hs hμs
  have h := ht (indicatorConstLp 2 hs hμs.ne 1)
  have he (v : RealL2 μ) : ⟪v,indicatorConstLp 2 hs hμs.ne 1⟫ = ∫ x in s, v x ∂μ := by
    rw [real_inner_comm,L2.inner_indicatorConstLp_one]
  simp_rw [he] at h
  exact ge_of_tendsto h (Eventually.of_forall fun n => integral_nonneg_of_ae (ae_restrict_of_ae (hf n)))

end EuclideanFiveColor
end
end OAI
