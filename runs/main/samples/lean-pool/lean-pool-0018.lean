@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment

@[reducible] local instance liftBaseOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

@[reducible] local instance liftOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

@[reducible] local instance liftSurvOrder (n : ℕ) :
    LinearOrder (SurvivingLabel
      (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) (cutL n) (cutR n)) :=
  sumLexSubtypeLinearOrder _ _ _

@[reducible] local instance liftTopOrder :
    LinearOrder (Fin 0 ⊕ Fin 0) :=
  sumLexLinearOrder _ _

open Classical in
theorem match_stepDataDown_congr_at_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (𝒟₁ 𝒟₂ : DataFamily (stepFragment n V)) {s : Finset V.Flag}
    (hm : ∀ (t : Finset (stepFragment n V).Flag),
      t = flagsOfEq
          (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_open n V hop)
          (V.dropSubset (cutL n) (cutR n) s) →
      ∀ (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
        (hEt : (EdgeSubset.mk t hct).Eulerian)
        (hnet : Nonempty (EdgeSubset.mk t hct).CanonData),
      (𝒟₁ t hct hEt hnet).1.MatchEq (𝒟₂ t hct hEt hnet).1)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) :
    (stepDataDown n V 𝒟₁ s hc hE hne).1.MatchEq
      (stepDataDown n V 𝒟₂ s hc hE hne).1 := by
  unfold stepDataDown
  rw [dite_eq_right hop, dite_eq_right hop]
  refine match_unglueDataOpen_congr_at (cutL_ne_cutR n) hop _ _
    ?_ hc hE hne
  intro hct hEt hnet
  refine match_dataOfEq_congr_at (gluePair_eq_open n V hop) _ _
    (V.dropSubset (cutL n) (cutR n) s) ?_ hct hEt hnet
  intro hc' hE' hne'
  exact match_relabelDataDown_congr_at (stepIso n) 𝒟₁ 𝒟₂ _
    (hm _ rfl) hc' hE' hne'

end EdgeSubset
end RS
end
