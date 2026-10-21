namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

section FullRelaxation

variable {n : ℕ} (W : Disorder n)

lemma exists_finite_poincare (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Spin n → ℝ, variance W f ≤ C * dirichlet W f := by
  classical
  let T : Finset ℝ := Finset.univ.image (fun p : Spin n × Spin n => (discreteKernel W ^ n) p.1 p.2)
  have hT : T.Nonempty := Finset.Nonempty.image Finset.univ_nonempty _
  let c := T.min' hT
  have hc : 0 < c := by
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp (Finset.min'_mem T hT)
    dsimp only [c]
    rw [← hp]
    exact discreteKernel_power_pos W hn p.1 p.2
  have hminor : ∀ x y, c * gibbs W y ≤ (discreteKernel W ^ n) x y := by
    intro x y
    calc
      _ ≤ c := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (gibbs_le_one W y) hc.le
      _ ≤ _ := Finset.min'_le T _ (Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, rfl⟩)
  refine ⟨c⁻¹, inv_pos.mpr hc, fun f => ?_⟩
  have hlow := kernel_energy_minorization W (discreteKernel W ^ n)
    (kernel_pow_sum (discreteKernel_sum W hn) n)
    (kernel_pow_stationary (discreteKernel_stationary W hn) n) hminor f
  have hup := discrete_inner_increment_le W hn n f
  rw [div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)), one_mul] at hup
  have hh : c * variance W f ≤ dirichlet W f := hlow.trans hup
  have := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh)
  simpa only [div_eq_mul_inv, mul_comm] using this

end FullRelaxation
end CriticalSK
end
end OAI
