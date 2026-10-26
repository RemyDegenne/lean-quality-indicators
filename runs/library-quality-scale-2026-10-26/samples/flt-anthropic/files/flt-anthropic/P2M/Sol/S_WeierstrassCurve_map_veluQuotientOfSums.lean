import Definitions.Def_WeierstrassCurve_VeluQuotientOfSums
import P2M.Util
namespace P2MW.S_WeierstrassCurve_map_veluQuotientOfSums

set_option autoImplicit false

open WeierstrassCurve

theorem solution
    {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {R' : Type*} [CommRing R'] (f : R →+* R') (t w : R) :
    (W.veluQuotientOfSums t w).map f = (W.map f).veluQuotientOfSums (f t) (f w) := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · exact W.map_a₁ f
  · exact W.map_a₂ f
  · exact W.map_a₃ f
  · simp only [veluQuotientOfSums_a₄, map_a₄, map_sub, map_mul, map_ofNat]
  · simp only [veluQuotientOfSums_a₆, map_a₆, map_b₂, map_sub, map_mul, map_ofNat]
