import Mathlib
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_finite_sections_not_le_preimage_of_smoothOfRelativeDimension_one
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth
attribute [-simp] AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {L : Type u} [Field L] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of L))
    [IsIntegral X] [SmoothOfRelativeDimension 1 c] [QuasiCompact c]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Set.Finite {q : Spec (CommRingCat.of L) ⟶ X |
      q ≫ c = 𝟙 (Spec (CommRingCat.of L)) ∧ ¬ ((⊤ : (Spec (CommRingCat.of L)).Opens) ≤ q ⁻¹ᵁ U)} := by
  classical
  have hfin : ((U : Set X)ᶜ).Finite := AlgebraicCurve.finite_compl_of_isOpen c U hU

  have hκ : ∀ q : Spec (CommRingCat.of L) ⟶ X, q ≫ c = 𝟙 (Spec (CommRingCat.of L)) →
      IsIso (c.residueFieldMap (q.base (IsLocalRing.closedPoint L))) := by
    intro q hq
    have hpt : c (q (IsLocalRing.closedPoint L)) = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    have hab : c.residueFieldMap (q.base (IsLocalRing.closedPoint L)) ≫ q.residueFieldMap (IsLocalRing.closedPoint L) =
        ((Spec (CommRingCat.of L)).residueFieldCongr hpt).hom := by
      rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr hq]
      simp
    haveI : Mono (q.residueFieldMap (IsLocalRing.closedPoint L)) :=
      ConcreteCategory.mono_of_injective _ (q.residueFieldMap (IsLocalRing.closedPoint L)).hom.injective
    haveI : IsSplitEpi (q.residueFieldMap (IsLocalRing.closedPoint L)) :=
      IsSplitEpi.mk' ⟨inv ((Spec (CommRingCat.of L)).residueFieldCongr hpt).hom ≫
        c.residueFieldMap (q.base (IsLocalRing.closedPoint L)), by simp [hab]⟩
    haveI : IsIso (q.residueFieldMap (IsLocalRing.closedPoint L)) := isIso_of_mono_of_isSplitEpi _
    exact IsIso.of_isIso_fac_right hab
  refine Set.Finite.of_finite_image
    (f := fun q : Spec (CommRingCat.of L) ⟶ X => q.base (IsLocalRing.closedPoint L)) ?_ ?_
  · refine hfin.subset ?_
    rintro _ ⟨q, ⟨hq₁, hq₂⟩, rfl⟩ hxU
    apply hq₂
    intro p _
    obtain rfl : p = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    exact hxU
  · intro q₁ hq₁ q₂ hq₂ hpt
    exact AlgebraicGeometry.eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap c q₁ q₂
      (hq₁.1.trans hq₂.1.symm) hpt (hκ q₁ hq₁.1)
