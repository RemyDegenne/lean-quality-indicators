section

@[expose] public section

noncomputable section

namespace NavierStokes.CandidateConsequences

open Set Filter Function ProblemStatement

open scoped ContDiff Topology BigOperators Pointwise

theorem futureJet_eq_full_of_pos {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain) {t : ℝ} (ht : 0 < t) (x : Space) (m : ℕ) :
    futureJet f m (t, x) = iteratedFDeriv ℝ m f (t, x) :=
  futureJet_eq_full ht.le x m
    (hf.contDiffAt (prod_mem_nhds (Ici_mem_nhds ht) univ_mem))

end NavierStokes.CandidateConsequences
end
end
end
