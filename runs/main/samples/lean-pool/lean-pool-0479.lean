@[expose] public section

noncomputable section

namespace NavierStokes.SignedCrossDefectClass

open Set WeightedClasses MeanIncrementBounds CorrectionState SignedMeanGain LabelSumBounds

open scoped ContDiff BigOperators

theorem defect_all_exponents (G : Geometry) {ι : Type} {P : ι → ℕ → Point → ℝ}
    {α δ β η : ℝ} (f : SignedFamily G.strip P α δ β η) (a : Assembly f)
    (hαδ : α ≤ δ) (i j : Fin 3) (e : ℕ) (r : MeanIncrementBounds.Field Point)
    (hS : SmoothOn G.domain (crossTensor f a i j))
    (hr : SmoothOn G.domain r)
    (hs : ∀ n, LocalSignedRequest.MovingSupport G.patch.a G.patch.b G.coord G.region.carrier (r n))
    (hc : MeanClass G.strip (α + β) r) (N : ℕ)
    (htail : ∀ n, N ≤ n → ∀ x ∈ G.strip.domain,
      StateMomentBalances.meanBar (crossTensor f a i j) n x = physicalSigma G e r n x) :
    ∀ γ : ℝ, MeanClass G.strip γ
      (StateMomentBalances.meanBar (crossTensor f a i j) - physicalSigma G e r) := by
  apply FiniteHeadClass.meanClass_all_exponents (defect_mem G f a hαδ i j e r hS hr hs hc) N
  intro n hn x hx
  simp only [Pi.sub_apply, htail n hn x hx, sub_self]

end NavierStokes.SignedCrossDefectClass
end
end
