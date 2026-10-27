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

section TorusTarget

variable [Fact p.Prime] (hp2 : p ≠ 2)
  (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D D' : LevelPData A) (hD : IsLevelPStructure W p D)
  (hD' : IsLevelPStructure W p D') {a b : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2)
  (hb : 1 ≤ b) (hb' : b ≤ (p - 1) / 2)
  (heqP : D'.xP * (W.ΨSq a).eval D.xP = (W.Φ a).eval D.xP)
  (heqQ : D'.xQ * (W.ΨSq b).eval D.xQ = (W.Φ b).eval D.xQ)

def torusTheta : TorusRing p a b →+* A :=
  TorusRing.lift p a b (UnivBasisRing.classify p W (hpA.mul hW) D hD) D'
    (isLevelPStructure_map_classify' p hpA W hW D D' hD hD')
    (xP_eq_classify_torusX p hpA hp2 W hW D D' hD ha ha' heqP)
    (xQ_eq_classify_borelX p hpA hp2 W hW D D' hD hb hb' heqQ)

end TorusTarget
end Targets
end QExpSplitDevissage
end ModularCurve
end
end P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field
