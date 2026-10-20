namespace P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_sum_archDeriv_rev_eq_casimir3_add_casimir1_casimir1_sub_three_smul_casimir2

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite archDeriv casimir1 casimir2 casimir3)

p2m_open

namespace LanglandsTunnell

namespace CubicInduction

namespace JointCubicAux

p2m_open

theorem archDeriv_sub {F G : G3 → ℂ} (hF : WhittakerBlock.IsArchSmooth3 F) (hG : WhittakerBlock.IsArchSmooth3 G)
    (i j : Fin 3) : archDeriv i j (F - G) = archDeriv i j F - archDeriv i j G := by
  rw [sub_eq_add_neg, archDeriv_add hF (sm_neg hG), archDeriv_neg, ← sub_eq_add_neg]

end JointCubicAux
end CubicInduction
end LanglandsTunnell
end P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_sum_archDeriv_rev_eq_casimir3_add_casimir1_casimir1_sub_three_smul_casimir2
