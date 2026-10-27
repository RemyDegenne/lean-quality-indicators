namespace P2MW.S_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation

attribute [-instance] ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option linter.unusedSectionVars false

set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField AlgebraicCurve

namespace LigozatUnitBar

open LigozatUnitEngine

variable (N p : ℕ) [NeZero N] [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ

local notation "kk" => IsLocalRing.ResidueField A

abbrev uInvA : LaurentSeries A := coeffMap (Int.castRingHom A) (unitInvInt p)

end LigozatUnitBar
end
end P2MW.S_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation
