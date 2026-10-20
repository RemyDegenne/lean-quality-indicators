namespace P2MW.S_FreyPackage_frey_wild_inertia_at_two_trivial

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace FreyWild

section ValueGroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

lemma one_lt_mul_self {a : Γ} (h : 1 < a) : 1 < a * a :=
  lt_trans h (lt_mul_self h)

end ValueGroup
end FreyWild
end P2MW.S_FreyPackage_frey_wild_inertia_at_two_trivial
