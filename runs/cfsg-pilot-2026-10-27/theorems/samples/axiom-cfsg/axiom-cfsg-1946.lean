public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL)

open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K]

theorem coe_qGammaInv (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (γ : DeterminantIsometries K) :
    (((qGammaInv h2 ha γ : CatalogueBGraphForm.isometryGroup 4 K (diagGL (qW_ne_zero ha))) :
      GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = qGamMat h2 ha γ := rfl

end CFSG.ComponentClassification.Burgoyne.O
end
