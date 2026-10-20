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

theorem PolynomialJets.neg {f : ι → E → F} (hf : PolynomialJets D f) :
    PolynomialJets D (fun i x => -f i x) := by
  simpa only [neg_apply, ContinuousLinearMap.id_apply] using hf.clm (-ContinuousLinearMap.id ℝ F)

end Calculus
end NavierStokes.PhaseJetBounds
end
end
end
