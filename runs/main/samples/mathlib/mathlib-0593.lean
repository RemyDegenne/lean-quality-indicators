public section

open MeasureTheory Measure ProbabilityTheory ENNReal

open scoped BoundedContinuousFunction

variable {Ω S T : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

variable {E : S → Type*} {F : T → Type*} {G H : Type*}
  [∀ s, TopologicalSpace (E s)] [∀ s, MeasurableSpace (E s)] [∀ s, BorelSpace (E s)]
  [∀ s, HasOuterApproxClosed (E s)]
  [∀ t, TopologicalSpace (F t)] [∀ t, MeasurableSpace (F t)] [∀ t, BorelSpace (F t)]
  [∀ t, HasOuterApproxClosed (F t)]
  [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [HasOuterApproxClosed G]
  [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [HasOuterApproxClosed H]
  {X : (s : S) → Ω → E s} {Y : (t : T) → Ω → F t} {Z : Ω → G} {U : Ω → H}

section Fintype

variable [Fintype S] [Fintype T]

section IndepFun

variable [IsFiniteMeasure P]

omit [Fintype T] in variable [Finite T] in
lemma indepFun_pi_of_bcf (mZ : AEMeasurable Z P)
    (mY : ∀ t, AEMeasurable (Y t) P)
    (h : ∀ (f : G →ᵇ ℝ) (g : (Π t, F t) →ᵇ ℝ),
      P[fun ω ↦ f (Z ω) * g (Y · ω)] = P[f ∘ Z] * P[fun ω ↦ g (Y · ω)]) :
    IndepFun Z (fun ω t ↦ Y t ω) P := by
  have := Fintype.ofFinite T
  refine indepFun_pi_of_prod_bcf mZ mY fun f g ↦ ?_
  convert! h f (∏ t, (g t).compContinuous ⟨Function.eval t, by fun_prop⟩) <;> simp

end IndepFun
end Fintype
end
