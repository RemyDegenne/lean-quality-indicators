public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIL

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {k : Type} [Field k]

theorem mU1_mulVec (x : Fin 4 → k) :
    (mU1 : Matrix (Fin 4) (Fin 4) k) *ᵥ x = ![x 0 + x 1 + 2 * x 2, x 1, x 2 + x 1, x 3] := by
  funext i
  fin_cases i
  all_goals simp [mU1, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  all_goals ring

end OIL
end CFSG.ComponentClassification.CatFactsL4U4
end
