import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
namespace P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_one_heq

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace VCOneGlue

theorem heq_some_of_eq {K : Type*} [Field K] {V V' : WeierstrassCurve.Affine K} (hV : V = V') {x y x' y' : K}
    (hx : x = x') (hy : y = y') (h : V.Nonsingular x y) (h' : V'.Nonsingular x' y') :
    HEq (Point.some x y h) (Point.some x' y' h') := by
  subst hV hx hy
  rfl

theorem heq_zero_of_eq {K : Type*} [Field K] {V V' : WeierstrassCurve.Affine K} (hV : V = V') :
    HEq (0 : V.Point) (0 : V'.Point) := by
  subst hV
  rfl

end VCOneGlue

open VCOneGlue in
theorem solution
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve.Affine K) (T : W.Point) :
    HEq (Point.vcInvFun (1 : VariableChange K) W T) T := by
  have h1 : (1 : VariableChange K) • W = W := one_smul _ _
  rcases T with _ | ⟨x, y, h⟩
  · exact heq_zero_of_eq h1
  · simp only [Point.vcInvFun]
    apply heq_some_of_eq h1
    · simp [vcXInv, VariableChange.one_def]
    · simp [vcYInv, VariableChange.one_def]
