import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_U_quadratic

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) :
    U π ^ 2 - S π * U π + const π π = 0 :=
  by
  rw [← ModularCurve.UVCrossingModel.U_mul_V, S_def]; ring
