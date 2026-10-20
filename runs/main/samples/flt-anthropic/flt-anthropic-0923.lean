namespace P2MW.S_WeierstrassProjModel_exists_pointEval

set_option Elab.async false

section MEGA_KwLRAffinePtSetEquiv_lean

set_option autoImplicit false

set_option maxHeartbeats 12800000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial

open HomogeneousLocalization HomogeneousIdealQuotientGrading

open scoped WeierstrassCurve.Projective

namespace WeierstrassProjModel

p2m_open

p2m_open

attribute [local instance] Classical.propDecidable

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R))

set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective

set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective

set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover

set_option quotPrecheck false in
local notation "gen" => kw_lrChart_gen W

set_option quotPrecheck false in
local notation "dehom" => kw_lrChart_dehom W

set_option quotPrecheck false in
local notation "t_F" => kw_lrAptb_tF (R := R) F

set_option quotPrecheck false in
local notation "awayι₃" i => Proj.awayι (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R)) (kw_pbac_mk_X_mem_one_CR R W.toProjective i) one_pos

set_option quotPrecheck false in
local notation "W_F" => kw_lrApt_WF W F

section ChartFactorization

theorem kw_lrApt_chartHom_fac (φ : SchemeHomOver (t_F) π) :
    φ.1 = Spec.map (CommRingCat.ofHom (kw_lrApt_chartHom W F φ).toRingHom)
            ≫ (coverE).f (kw_lrApt_chartIdx W F φ) :=
  (kw_lrApt_schemeHom_factor W F φ).choose_spec.choose_spec

end ChartFactorization
end WeierstrassProjModel
end
end MEGA_KwLRAffinePtSetEquiv_lean
end P2MW.S_WeierstrassProjModel_exists_pointEval
