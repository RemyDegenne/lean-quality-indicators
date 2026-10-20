@[expose] public section

noncomputable section

namespace NavierStokes.SignedCopyBounds

open Set Function Filter WeightedClasses PeriodizedWaveBounds

open scoped ContDiff Topology BigOperators

variable {D E F G I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

section LocalOperations

variable {s : StripData D} {K : ℕ → I → Set D} {w v : ℕ → D → ℝ} {α β : ℝ}

theorem local_mul {f g : ℕ → I → D → ℝ}
    (hf : LocalJets s w α K f) (hg : LocalJets s v β K g)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hv : ∀ n x, x ∈ s.domain → 0 ≤ v n x) :
    LocalJets s (fun n x => w n x * v n x) (α + β) K (fun n i x => f n i x * g n i x) := by
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    hf.bilinear hg (ContinuousLinearMap.lsmul ℝ ℝ) hw hv

end LocalOperations
end NavierStokes.SignedCopyBounds
end
end
