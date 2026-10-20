public section

namespace TauCeti.Huber

open Filter

section Comparison

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CompleteSpace (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
    isWeightFamily_one_weight)]
  [T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)]

variable (k A) in
/-- **The comparison equivalence of roadmap Layer 0.5**: when the plain restricted-series ring
is complete and Hausdorff, the completed restricted power-series algebra `A⟨X₁,…,Xₖ⟩` is that
ring. -/
noncomputable def restrictedMvPowerSeriesCompletionEquiv :
    restrictedMvPowerSeriesCompletion k A ≃+*
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  UniformSpace.Completion.completeRingEquivSelf _

end Comparison
end TauCeti.Huber
end
