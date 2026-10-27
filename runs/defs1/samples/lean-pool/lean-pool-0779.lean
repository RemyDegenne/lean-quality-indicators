@[expose] public section

namespace Bananas

open Utilities

/-- The finite rank-drop sum in the final, unlabelled proposition of Section
5.  This is the paper's sum over a fundamental domain `[k]`, encoded by
`Fin k`. -/
noncomputable def sectionFiveRankDropSum
    (M : TwiceMarked) (D : CFDiv M.graph) (k : ℕ) : ℤ :=
  ∑ m : Fin k,
    (rank M.graph
        (D + ((((m : ℕ) : ℤ) - 1) • oneChip M.u) -
          ((m : ℕ) : ℤ) • oneChip M.v) -
      rank M.graph
        (D + ((((m : ℕ) : ℤ) - 2) • oneChip M.u) -
          ((m : ℕ) : ℤ) • oneChip M.v))

end Bananas
end
