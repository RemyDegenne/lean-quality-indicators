namespace OAI

noncomputable section

namespace ContinuumCoulomb.QuantumRawExchange

theorem mass_bound (xs : List Raw) {B : ℝ} (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B) :
    (mass xs:ℝ) ≤ xs.length*B := by
  induction xs with
  | nil => simp [mass]
  | cons t xs ih =>
    have ht := hw t (by simp)
    have hs := ih (by intro u hu; exact hw u (by simp [hu]))
    simp only [mass,List.map_cons,List.sum_cons,Rat.cast_add,Rat.cast_abs,
      List.length_cons,Nat.cast_add,Nat.cast_one]
    change |(t.2.2.2:ℝ)|+(mass xs:ℝ) ≤ _
    nlinarith

end ContinuumCoulomb.QuantumRawExchange
end
end OAI
