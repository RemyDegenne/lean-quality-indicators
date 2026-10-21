namespace OAI

open Erdos970

noncomputable section

open scoped BigOperators Classical

namespace Ostmann.Arithmetic.HistoryGiantReferenceMean

open Construction HistorySignedXiTransport HistorySignedDecode HistorySignedResidues

open HistorySupportReduction HistorySymbolicEncoding

theorem weightedMean_zero_of_no_reference {α : Type*} [Fintype α] (d : Decomposition)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c e : HistoryChoices sources seed V l)
    (P Q : α→ℤ) (w : α→ℝ) (J : α→ℂ) (bc sc : ℕ) (X tb td G : ℝ)
    (hw : ∀i,0 ≤ w i)
    (hn : ¬∃i,0 < w i ∧ (drawHistory sources seed V l a c P Q i).Supported V outside ∧
      (drawHistory sources seed V l b e P Q i).Supported V outside) :
    weightedMean d sources seed V outside l a b c e P Q w J bc sc X tb td G=0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : w i=0
  · simp only [hi,Complex.ofReal_zero,zero_mul]
  · have hnot : ¬((drawHistory sources seed V l a c P Q i).Supported V outside ∧
        (drawHistory sources seed V l b e P Q i).Supported V outside) :=
      fun hh => hn ⟨i,lt_of_le_of_ne (hw i) (Ne.symm hi),hh⟩
    rw [supportedHistoryPairXi_eq_zero_of_not d V outside bc sc X tb td G _ _ hnot,mul_zero]

end Ostmann.Arithmetic.HistoryGiantReferenceMean
end
end OAI
