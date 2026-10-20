namespace P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot

attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option autoImplicit false

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace ModularCurve

p2m_open

namespace P2MToricLevel

universe u v

section Toric

variable (K : Type u) [Field K] {ζ : K}

theorem relations_R_one (c : (Rz K ζ)ˣ) (h1c : IsUnit (1 - (c : Rz K ζ)))
    (h1ci : IsUnit (1 - ((c⁻¹ : (Rz K ζ)ˣ) : Rz K ζ))) (hc1 : (c : Rz K ζ) ≠ 1) :
    (tateLaurent (Rz K ζ)).toAffine.Equation (tateToricPoint (Rz K ζ) 1 c).1
        (tateToricPoint (Rz K ζ) 1 c).2 ∧
    negRel (tateLaurent (Rz K ζ)) (tateToricPoint (Rz K ζ) 1 c).1 (tateToricPoint (Rz K ζ) 1 c).2
        (tateToricPoint (Rz K ζ) 1 c⁻¹).1 (tateToricPoint (Rz K ζ) 1 c⁻¹).2 := by
  classical
  let ι : Rz K ζ →+* Fz K ζ := algebraMap (Rz K ζ) (Fz K ζ)
  let ιL : LaurentSeries (Rz K ζ) →+* LaurentSeries (Fz K ζ) := coeffMap ι
  have hιinj : Function.Injective ι := IsFractionRing.injective (Rz K ζ) (Fz K ζ)
  have hιLinj : Function.Injective ιL := coeffMap_injective ι hιinj
  have hW : (tateLaurent (Rz K ζ)).map ιL = tateLaurent (Fz K ζ) := tateLaurent_map ι
  have hne0 : ∀ u : (Rz K ζ)ˣ, ι u ≠ 0 := fun u => (map_ne_zero_iff ι hιinj).mpr u.ne_zero
  have hne1 : ∀ {u : (Rz K ζ)ˣ}, (u : Rz K ζ) ≠ 1 → ι u ≠ 1 := fun hu h =>
    hu (hιinj (h.trans (map_one ι).symm))
  have hci1 : ((c⁻¹ : (Rz K ζ)ˣ) : Rz K ζ) ≠ 1 := by
    intro h; apply hc1
    have h2 : c⁻¹ = 1 := Units.ext h
    rw [← inv_inv c, h2, inv_one, Units.val_one]
  have hx : ∀ (u : (Rz K ζ)ˣ), IsUnit (1 - (u : Rz K ζ)) →
      ιL (tateToricPoint (Rz K ζ) 1 u).1 = (toricPoint (Fz K ζ) 1 (ι u)).1 := fun u hu =>
    coeffMap_frac_toric_fst K u hu
  have hy : ∀ (u : (Rz K ζ)ˣ), IsUnit (1 - (u : Rz K ζ)) →
      ιL (tateToricPoint (Rz K ζ) 1 u).2 = (toricPoint (Fz K ζ) 1 (ι u)).2 := fun u hu =>
    coeffMap_frac_toric_snd K u hu
  have hιinv : ι c * ι ((c⁻¹ : (Rz K ζ)ˣ) : Rz K ζ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]

  obtain ⟨hcF, hciF, hinv, -⟩ := ModularCurve.toricPoint_add_toricPoint_of_charZero (Fz K ζ) (ι c)
    (ι ((c⁻¹ : (Rz K ζ)ˣ) : Rz K ζ)) (hne0 c) (hne0 c⁻¹) (hne1 hc1) (hne1 hci1)
  refine ⟨?_, ?_⟩
  ·
    have h : ((tateLaurent (Rz K ζ)).map ιL).toAffine.Equation (ιL (tateToricPoint (Rz K ζ) 1 c).1)
        (ιL (tateToricPoint (Rz K ζ) 1 c).2) := by
      rw [hW, hx c h1c, hy c h1c]; exact hcF.left
    exact (map_equation _ hιLinj _ _).mp h
  ·
    have h : negRel ((tateLaurent (Rz K ζ)).map ιL) (ιL (tateToricPoint (Rz K ζ) 1 c).1)
        (ιL (tateToricPoint (Rz K ζ) 1 c).2) (ιL (tateToricPoint (Rz K ζ) 1 c⁻¹).1)
        (ιL (tateToricPoint (Rz K ζ) 1 c⁻¹).2) := by
      rw [hW, hx c h1c, hy c h1c, hx c⁻¹ h1ci, hy c⁻¹ h1ci]
      exact negRel_of_add_eq_zero (hinv hιinv)
    exact negRel_of_map ιL _ hιLinj h

end Toric
end P2MToricLevel
end ModularCurve
end
end P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
