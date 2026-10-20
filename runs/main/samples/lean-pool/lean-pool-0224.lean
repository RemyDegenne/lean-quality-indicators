@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

theorem exists_support_direction_of_not_rankTwo
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    {r : Fin 2 →₀ ℕ} (hr : r ∈ f.support)
    (hnrank : ¬ PlaneCurveSupportHasRankTwo f)
    (hnonsingleton : ∃ s ∈ f.support, s ≠ r) :
    ∃ v : Fin 2 → ℤ, v ≠ 0 ∧
      ∀ s ∈ f.support, ∃ k : ℤ,
        planeExponentDifference r s = k • v := by
  obtain ⟨s, hs, hsr⟩ := hnonsingleton
  have hd : planeExponentDifference r s ≠ 0 := by
    intro h
    apply hsr
    apply Finsupp.ext
    intro i
    have hi := congrFun h i
    dsimp [planeExponentDifference] at hi
    omega
  obtain ⟨v, hv⟩ := integerVectorLine_cyclic hd
  have hparam : ∀ t ∈ f.support, ∃ k : ℤ,
      planeExponentDifference r t = k • v := by
    intro t ht
    apply hv
    rw [integerVectorDet_planeExponentDifference]
    by_contra hdet
    exact hnrank ⟨r, s, t, hr, hs, ht, hdet⟩
  have hvne : v ≠ 0 := by
    obtain ⟨k, hk⟩ := hparam s hs
    intro hv0
    apply hd
    simpa [hv0] using hk
  exact ⟨v, hvne, hparam⟩

end
end BGS.CorvajaZannier
end
