public section

namespace TauCeti.TerminalCut

open Finset

variable {V W K : Type*}

section Extremal

variable [DecidableEq V] [Finite V] [AddCommMonoid K] [LinearOrder K]
  [IsOrderedCancelAddMonoid K]

variable {f : Finset V → K} (hf : IsSubmodular f) {A B : Finset V}

include hf

@[simp] theorem coe_bot_minimizers (hAB : Disjoint A B) :
    letI := minimizersBoundedOrder hf hAB
    ((⊥ : minimizers hf A B) : Finset V) = smallest hf hAB := by
  let := minimizersBoundedOrder hf hAB
  symm
  apply (smallest_eq_iff hf hAB).mpr
  exact ⟨(⊥ : minimizers hf A B).property, fun T hT ↦
    Subtype.coe_le_coe.mpr (bot_le (a := (⟨T, hT⟩ : minimizers hf A B)))⟩

end Extremal
end TauCeti.TerminalCut
end
