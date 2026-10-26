import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Theorems.Thm_Rep_exact_tateH0Map_tateH0Map
import Theorems.Thm_Rep_exact_tateHneg1Map_tateHneg1Map
import P2M.Util
namespace P2MW.S_Rep_exact_tateMap_tateMap

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    Function.Exact (Rep.tateMap X.f n).hom (Rep.tateMap X.g n).hom := by
  match n with
  | Int.ofNat (m + 1) =>
    exact LinearMap.exact_iff.2 (groupCohomology.mapShortComplex₂_exact hX (m + 1)).moduleCat_range_eq_ker.symm
  | Int.ofNat 0 => exact Rep.exact_tateH0Map_tateH0Map hX
  | Int.negSucc 0 => exact Rep.exact_tateHneg1Map_tateHneg1Map hX
  | Int.negSucc (m + 1) =>
    exact LinearMap.exact_iff.2 (groupHomology.mapShortComplex₂_exact hX (m + 1)).moduleCat_range_eq_ker.symm
