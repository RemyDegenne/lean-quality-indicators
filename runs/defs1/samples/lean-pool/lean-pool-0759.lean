@[expose] public section

namespace Bananas

open Utilities

/-- The paper's nonrecurrence condition, formulated on concrete torsion
residues instead of Picard-group quotient classes. -/
def NonRecurrent (M : TwiceMarked) (k : ℕ) : Prop :=
  ∀ (w : M.graph.V) (n m : Fin k), n.val ≠ 0 → m.val ≠ 0 →
    0 ≤ rank M.graph
      (oneChip w + (n.val : ℤ) • (oneChip M.u - oneChip M.v)) →
    0 ≤ rank M.graph
      (oneChip w + (m.val : ℤ) • (oneChip M.u - oneChip M.v)) →
    n = m

end Bananas
end
