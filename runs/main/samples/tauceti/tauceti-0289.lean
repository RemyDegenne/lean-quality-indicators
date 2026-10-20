public section

namespace TauCeti.TypeDStd

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [DecidableEq ι]

section Fintype

variable [CommRing K] [Fintype ι]

theorem negSumRootGenerator_reverse_fork_eq_rootGenerator (n : ℕ) (hn : 4 ≤ n) :
    negSumRootGenerator (K := K) (forkRight n hn) (forkLeft n hn) =
      rootGenerator (K := K) n hn (.inr (forkRight n hn)) := by
  apply Subtype.ext
  rw [val_negSumRootGenerator, val_rootGenerator_inr]
  have hfork : ¬((forkRight n hn : Fin n) : ℕ) + 1 < n := by
    rw [forkRight_val]
    omega
  rw [loweringMatrix_of_fork n hn hfork]
  ext (a | a) (b | b) <;>
    simp [negSumRootMatrix, Matrix.fromBlocks, Matrix.single_apply]

end Fintype
end TauCeti.TypeDStd
end
