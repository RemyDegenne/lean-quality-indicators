namespace OAI

namespace ThorpNine.SparseSaving

namespace Thorp.Specht

open scoped BigOperators Classical

@[simp] lemma permSign_mul {α : Type*} [Fintype α] [DecidableEq α] (p q : Equiv.Perm α) :
    permSign (p*q) = permSign p * permSign q := by simp [permSign]

end Thorp.Specht
end ThorpNine.SparseSaving
end OAI
