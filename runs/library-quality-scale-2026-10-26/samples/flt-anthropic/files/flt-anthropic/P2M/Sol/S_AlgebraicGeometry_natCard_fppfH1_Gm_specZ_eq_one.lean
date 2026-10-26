import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Theorems.Thm_AlgebraicGeometry_subsingleton_fppfH1_Gm_specZ
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_natCard_fppfH1_Gm_specZ_eq_one
attribute [-simp] Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul
p2m_open "CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry"
theorem solution :
    Nat.card (FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1) = 1 := by
  haveI := AlgebraicGeometry.subsingleton_fppfH1_Gm_specZ
  have h0 : Nonempty (FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1) := ⟨0⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, h0⟩
