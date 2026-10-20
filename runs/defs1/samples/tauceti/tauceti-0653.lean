public section

namespace TauCeti.ConstructionA

variable (m : ℕ) [NeZero m] (ι : Type*) [Fintype ι]

variable (hm : Even m)

/-- **The discriminant quadratic module of an even Construction A lattice is `C⊥ / C`.** Over an
even modulus, for a quadratically isotropic code `C`, the discriminant quadratic module of the
even lattice `P_m(C)` is the quadratic orthogonal quotient of `C` in the coordinate alphabet
`(ℤ/m)^ι`, in the half-norm convention. -/
noncomputable def discriminantOrthogonalQuotientIsometry (C : AdditiveCode (ZMod m) ι)
    (hC : ((FiniteQuadraticModule.zmodStandard m hm).coordinatePower ι).IsIsotropic C) :
    FiniteQuadraticModule.Isometry
      ((integralLattice m C
          ((isIsotropic_coordinatePower_zmodStandard_iff_le_euclideanDual m C).mp
            hC.toFiniteBilinearModule)).discriminantQuadraticModule
        ((isEven_integralLattice_iff_isIsotropic m hm C _).mpr hC))
      (((FiniteQuadraticModule.zmodStandard m hm).coordinatePower ι).orthogonalQuotient
        C hC) :=
  ((IntegralLattice.Isometry.ofEq
      (toIntegralLattice_codeInZeroLatticeDiscriminantGroup_eq_integralLattice m ι C _).symm
    ).discriminantQuadraticIsometry
      ((isEven_integralLattice_iff_isIsotropic m hm C _).mpr hC)).trans
    (((zeroLattice m ι).discriminantOrthogonalQuotientIsometryOfSubgroup
        (isEven_zeroLattice m ι hm)
        ((isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_iff m ι hm C).mpr hC)).trans
      ((discriminantQuadraticIsometry m ι hm).orthogonalQuotientEquiv
        ((isIsotropic_codeInZeroLatticeDiscriminantQuadraticModule_iff m ι hm C).mpr hC)
        (by
          rw [← FiniteQuadraticModule.Isometry.toFiniteBilinearModule_toAddEquiv,
            discriminantQuadraticIsometry_toFiniteBilinearModule,
            codeInZeroLatticeDiscriminantGroup_eq_codeInZeroLatticeDiscriminantBilinearModule]
          exact map_codeInZeroLatticeDiscriminantBilinearModule m ι C)))

end TauCeti.ConstructionA
end
