namespace P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le

attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

namespace KTORDAlpha

open ModularCurve

variable {K K' : Type*} [CommRing K] [CommRing K'] (h : K →+* K')

theorem alpha_main (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    ((tateBase K' p).preΨ p).eval (nonToricPoint K' p (Units.map (h : K →* K') c) j).1 =
      laurentMap h (((tateBase K p).preΨ p).eval (nonToricPoint K p c j).1) := by
  rw [← laurentMap_nonToricPoint_fst h p c j hj hjp, ← map_tateBase h p,
    WeierstrassCurve.map_preΨ, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (laurentMap h) _

end KTORDAlpha
end P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le
