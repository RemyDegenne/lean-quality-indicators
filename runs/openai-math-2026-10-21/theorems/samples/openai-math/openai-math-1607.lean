namespace OAI

noncomputable section

open scoped BigOperators

namespace Cotype

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem rowIndex_injective (i : ι) : Function.Injective (rowIndex (κ := κ) i) := by
  intro p q h
  funext j
  simpa using congrFun h (i,j)

end Cotype
end
end OAI
