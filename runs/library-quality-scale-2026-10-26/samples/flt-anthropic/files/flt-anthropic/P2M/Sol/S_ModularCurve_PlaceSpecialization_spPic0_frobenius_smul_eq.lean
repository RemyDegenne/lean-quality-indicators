import Definitions.Def_ModularCurve_PlaceSpecialization
import P2M.Util
namespace P2MW.S_ModularCurve_PlaceSpecialization_spPic0_frobenius_smul_eq

open AlgebraicCurve ModularCurve

theorem solution {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    [IsAlgClosed k] [IsCurveOver k (modularFunctionFieldC k N)]
    (S : PlaceSpecialization A ℓ N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) (x : JZero N) :
    S.spPic0 (σ • x) = frobeniusPushforwardGeomLevelPic0OfIsCurveOver k N data hKr (S.spPic0 x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  obtain ⟨D', hD', h'⟩ := S.spPic0_compat D
  rw [h', frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk, galois_smul_pic0_def,
    SemilinearAut.pic0_smul_mk]
  obtain ⟨D'', hD'', h''⟩ := S.spPic0_compat
    (SemilinearAut.degZeroSMulHom (arithmeticGalois (modularFunctionFieldFull N) σ) D)
  rw [h'']
  congr 1
  refine Subtype.ext ?_
  rw [hD'', coe_frobeniusPushforwardGeomLevelDegZero, hD', SemilinearAut.coe_degZeroSMulHom,
    SemilinearAut.divisor_smul_def, frobeniusPushforwardGeomLevel,
    Finsupp.mapDomain.addMonoidHom_apply, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr ?_
  intro w _
  exact S.d6_frobenius σ hσ w
