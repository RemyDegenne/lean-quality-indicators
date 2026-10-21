namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section

open scoped BigOperators

namespace Ostmann.Arithmetic.HistoryBulkFibreOriginalReference

open Construction Conclusion HistoryGiantReferenceMean

open HistoryBulkSourceDisintegration

open HistoryGiantOriginalMeanFactorization (Seed Current Choices)

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

variable (C : InitialSourceChoice d Bs BD Bz k L E)

variable (outside : List ℕ)

variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))

variable (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C)

theorem mixedFibreMean_eq_weighted :
    mixedFibreMean C outside σ a s t c e =
      HistoryBulkFibreReference.originalMean (selectedBulkPrior C l).mass
        (mixedWeight C.giantCenter C.giant)
        (fun y r => fibreTerm C outside σ a s t c e y
          (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r)) := by
  simp only [mixedFibreMean,mixedMean_eq_weighted,FinitePrior.cmean,
    HistoryBulkFibreReference.originalMean,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]

end Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
end
end OAI
