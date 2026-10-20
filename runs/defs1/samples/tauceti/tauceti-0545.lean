public section

namespace TauCeti.BinaryGolay

/-- The discriminant bilinear module of the Golay Construction A lattice is the actual orthogonal
quotient of its code. -/
noncomputable def discriminantBilinearOrthogonalQuotientIsometry :
    FiniteBilinearModule.Isometry constructionALattice.discriminantBilinearModule
      (((FiniteBilinearModule.zmodStandard 2).coordinatePower (Fin 24)).orthogonalQuotient
        code.toAddSubgroup) := by
  let hC := (TwoPowCode.isTypeII_one_iff.mpr isTypeII_code).le_euclideanDual
  letI : (ConstructionA.integralLattice 2 code.toAddSubgroup hC).IsNondegenerate :=
    ConstructionA.isNondegenerate_integralLattice 2 code.toAddSubgroup hC
  have hfirst : constructionALattice.discriminantBilinearModule.Isometry
      (ConstructionA.integralLattice 2 code.toAddSubgroup hC).discriminantBilinearModule :=
    (IntegralLattice.Isometry.ofEq
      constructionALattice_eq_integralLattice).discriminantBilinearIsometry
  exact hfirst.trans
    (ConstructionA.discriminantBilinearOrthogonalQuotientIsometry 2 (Fin 24) code.toAddSubgroup hC)

end TauCeti.BinaryGolay
end
