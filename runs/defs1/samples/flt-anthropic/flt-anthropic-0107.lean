namespace P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field

attribute [-instance] WeierstrassCurve.Generic.isElliptic_curve WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv

set_option autoImplicit false

universe u

noncomputable section

p2m_open

namespace ModularCurve

namespace QExpSplitDevissage

p2m_open

p2m_open

open scoped TensorProduct

section Targets

variable (p : ℕ) (S : Type u) [CommRing S] {A : Type u} [CommRing A] [Algebra S A]
  (hpA : IsUnit (p : A))

section VCTarget

variable (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A) (hD : IsLevelPStructure W p D)
  (C : VariableChange A) (hW' : IsUnit (C • W).Δ) (hD' : IsLevelPStructure (C • W) p (D.variableChange C))

def vcTheta : VCRing p →+* A := VCRing.lift p (UnivBasisRing.classify p W (hpA.mul hW) D hD) C

end VCTarget
end Targets
end QExpSplitDevissage
end ModularCurve
end
end P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field
