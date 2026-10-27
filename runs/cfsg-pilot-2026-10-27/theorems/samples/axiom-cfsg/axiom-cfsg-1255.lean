public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open WithConv

variable {k : Type} [Field k] [IsAlgClosed k]
  {ι : Type} [Fintype ι] [DecidableEq ι]

omit [IsAlgClosed k] in
theorem glCoord_smooth : Algebra.Smooth k (GLCoord k ι) := by
  let R := MvPolynomial (ι × ι) k
  let B := Localization.Away (matCoordDet k ι)
  have : Algebra.Smooth R B :=
    Algebra.Smooth.of_isLocalization_Away (matCoordDet k ι)
  have : Algebra.Smooth k R := inferInstance
  have : Algebra.Smooth k B := Algebra.Smooth.comp k R B
  exact Algebra.Smooth.of_equiv (glCoordEquivLocalization k ι).symm

end CFSG.LieType.AlgebraicGroups
end
