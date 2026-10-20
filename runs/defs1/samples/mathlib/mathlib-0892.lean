@[expose] public section

open List

open DyckStep

namespace DyckWord

variable {p q : DyckWord}

variable (h : p ≠ 0)

section BinaryTree

open BinaryTree

/-- Equivalence between Dyck words of semilength `n` and rooted binary trees with
`n` internal nodes. -/
@[simps!]
def equivTreesOfNumNodesEq (n : ℕ) : { p : DyckWord // p.semilength = n } ≃ treesOfNumNodesEq n :=
  equivTree.subtypeEquiv (by simp)

end BinaryTree
end DyckWord
end
