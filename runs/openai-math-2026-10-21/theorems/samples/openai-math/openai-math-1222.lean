namespace OAI

section

section

open MeasureTheory Set Filter

open scoped BigOperators ENNReal NNReal Classical

noncomputable section

namespace Coulomb

lemma coreConditionalObservable_raw_positive_weight {m k : ℕ} (u : H1Vector (m+k))
    (V : ℝ) {A : Set Space} (hA : MeasurableSet A) (y : Space) {r : ℝ}
    (hr : 0 < r) (hsep : ∀ v ∈ A, r ≤ ‖v-y‖) (s : Spins m) (x : Configuration m) :
    mass (u.coreSlice s x)*(max (coreConditionalObservable u (rawSignedField V A y) s x) 0)^2 =
      mass (u.coreSlice s x)*(max (V-restrictedCorePotential (u.coreSlice s x).normalized A y-
        restrictedOutPotential x A y) 0)^2 := by
  by_cases h : mass (u.coreSlice s x)=0
  · simp only [h,zero_mul]
  · rw [coreConditionalObservable_rawSignedField u V hA y hr hsep s x
      (lt_of_le_of_ne (mass_nonneg _) (Ne.symm h))]

end Coulomb
end
end
end
end OAI
