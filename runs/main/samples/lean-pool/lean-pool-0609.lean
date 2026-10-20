section

@[expose] public section

noncomputable section

namespace NavierStokes.PhaseJetBounds

open Set

open scoped Topology ContDiff InnerProductSpace

section Calculus

variable {ι E F G H : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [NormedAddCommGroup G] [NormedSpace ℝ G]

variable [NormedAddCommGroup H] [NormedSpace ℝ H]

variable {D : Domain ι E}

theorem PolynomialJets.const (c : ι → F) {C : ℝ} {m : ℕ} (hC : 1 ≤ C)
    (hc : ∀ i, ‖c i‖ ≤ C * D.scale i ^ m) :
    PolynomialJets D (fun i _ => c i) := by
  refine ⟨fun _ => contDiffOn_const, fun _ => ⟨C, hC, m, ?_⟩⟩
  intro i n hn x hx
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hc i
  | succ n =>
      rw [iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply, norm_zero]
      exact mul_nonneg (le_trans zero_le_one hC)
        (pow_nonneg (le_trans zero_le_one (D.one_le_scale i)) _)

end Calculus
end NavierStokes.PhaseJetBounds
end
end
end
