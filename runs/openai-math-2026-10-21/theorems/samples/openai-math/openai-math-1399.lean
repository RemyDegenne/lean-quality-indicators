namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceRankPhase

open Turing Complexity

open scoped BigOperators

open Target SourceContexts SourceOccurrences SourceAddressArithmetic

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

omit [DecidableEq K] in
theorem clean_reverseSlots (slots : MachineHorner.Layout width ↪ K) (base : K → List Bool)
    (clean : MachineHorner.Clean slots base) : MachineHorner.Clean (reverseSlots slots) base where
  accA := by simpa only [reverseSlots_control] using clean.accA
  accB := by simpa only [reverseSlots_control] using clean.accB
  counter := by simpa only [reverseSlots_control] using clean.counter
  scratch := by simpa only [reverseSlots_control] using clean.scratch

end MinUncutGames.Foundations.Hastad.SourceRankPhase
end OAI
