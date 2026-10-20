namespace P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul

set_option Elab.async false

p2m_reactivate

p2m_reactivate

section MEGA_EvalBridge

noncomputable section

p2m_open

namespace WeierstrassProjModel

p2m_open

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R]

variable (W : WeierstrassCurve R) (F : Type u) [Field F] [Algebra R F]

noncomputable def kw_ev_e (hΔF : algebraMap R F W.Δ ≠ 0) :
    SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective) → (kw_lrApt_WF W F).Point :=
  (WeierstrassProjModel.exists_pointEval W F hΔF).2.2.choose

end WeierstrassProjModel
end
end MEGA_EvalBridge
end P2MW.S_WeierstrassProjModel_addMorphism_zeroSect_mul
