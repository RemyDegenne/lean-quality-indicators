namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

attribute [local instance] Classical.propDecidable

lemma gridPartialSweep_path {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (g : GridChoices bits) (hg : pathEvent H g)
    (t : Fin (b+1)) (i : Fin h) :
    gridPartialSweep bits g t (H.position 0 i) = H.position t i := by
  induction t using Fin.induction with
  | zero => simp
  | succ j ih => rw [gridPartialSweep_succ, Equiv.Perm.mul_apply, ih, hg j i]

end BinaryCoordinateSweeps
end
end OAI
