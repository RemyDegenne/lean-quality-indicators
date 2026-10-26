import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_of_edgeNondegAt_maximalIdeal

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] [IsLocalRing B]
    (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K)
    (h : d.EdgeNondegAt π (IsLocalRing.maximalIdeal B) M' M) :
    d.InEdgeChart π M' M := by
  intro 𝔭 h𝔭
  have hsub : 𝔭 ≤ IsLocalRing.maximalIdeal B := IsLocalRing.le_maximalIdeal h𝔭.ne_top
  obtain ⟨hle, hπ, h1, h2⟩ := h
  refine ⟨hle, hπ, fun v hv hmem => h1 v hv ?_, fun v' hv' hmem => h2 v' hv' ?_⟩
  · have hmono : d.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) ≤
        d.line M ⊔ (IsLocalRing.maximalIdeal B • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) :=
      sup_le_sup_left (Submodule.smul_mono_left hsub) _
    exact hmono hmem
  · have hmono : d.line M' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')) ≤
        d.line M' ⊔ (IsLocalRing.maximalIdeal B • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')) :=
      sup_le_sup_left (Submodule.smul_mono_left hsub) _
    exact hmono hmem
