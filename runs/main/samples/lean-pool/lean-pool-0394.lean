@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment

@[reducible] local instance famBaseOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

@[reducible] local instance famOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

@[reducible] local instance famSurvOrder (n : ℕ) :
    LinearOrder (SurvivingLabel
      (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) (cutL n) (cutR n)) :=
  sumLexSubtypeLinearOrder _ _ _

@[reducible] local instance famTopOrder :
    LinearOrder (Fin 0 ⊕ Fin 0) :=
  sumLexLinearOrder _ _

open Classical in
theorem isOut_pushData_liftData_succ_closed_at (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (bits : Fin (n + 1) → Bool) (𝒟 : DataFamily V)
    {s : Finset V.Flag} (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData)
    (hbit : bits (Fin.last n)
      = decide (V.boundaryFlag (cutL n) ∈ s))
    (hIH : ∀ (t : Finset (stepFragment n V).Flag),
      t = flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_closed n V hcl)
          (V.dropSubset (cutL n) (cutR n) s) →
      ∀ (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
        (hEt : (EdgeSubset.mk t hct).Eulerian)
        (hnet : Nonempty (EdgeSubset.mk t hct).CanonData)
        (g : (stepFragment n V).Flag),
      (∀ b, g ≠ (stepFragment n V).boundaryFlag b) →
      (pushData n (stepFragment n V)
          (liftData n (stepFragment n V)
            (fun a => bits a.castSucc)
            (stepDataUp n V (bits (Fin.last n)) 𝒟))
          t hct hEt hnet).2.isOut g
        = (stepDataUp n V (bits (Fin.last n)) 𝒟 t hct hEt
          hnet).2.isOut g)
    (hcL : ∀ f ∈ liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s)),
      V.pairing f ∈ liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s)))
    (hEL : (EdgeSubset.mk (liftSubsetClosed
      (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
      EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk (liftSubsetClosed
      (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
      EdgeSubset V).CanonData)
    (f : V.Flag) (hfb : ∀ a, f ≠ V.boundaryFlag a) :
    (pushData (n + 1) V (liftData (n + 1) V bits 𝒟) s hc hE
        hne).2.isOut f = (𝒟 s hc hE hne).2.isOut f := by
  have h1 : f ≠ V.boundaryFlag (cutL n) := hfb _
  have h2 : f ≠ V.boundaryFlag (cutR n) := hfb _
  have h3 := isOut_stepDataDown_congr_at_closed n V hcl
    (pushData n (stepFragment n V)
      (liftData n (stepFragment n V) (fun a => bits a.castSucc)
        (stepDataUp n V (bits (Fin.last n)) 𝒟)))
    (stepDataUp n V (bits (Fin.last n)) 𝒟) hIH hc hE hne f hfb
  rw [stepData_roundTrip_closed n V hcl (bits (Fin.last n)) 𝒟] at h3
  have h4 := isOut_unglue_glueDataClosed (cutL_ne_cutR n) hcl 𝒟 hc
    hE hne hcL hEL hneL f h1 h2
  rw [← hbit] at h4
  exact h3.trans h4

end EdgeSubset
end RS
end
