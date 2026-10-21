namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal

noncomputable section

open Finset

section Molecules

variable (S : Type*)

variable {S}

@[simp] theorem molecule_self (s : S) : molecule s s = 0 := by
  apply Subtype.ext
  simp [molecule]

end Molecules
end
end C0Absorption
end OAI
