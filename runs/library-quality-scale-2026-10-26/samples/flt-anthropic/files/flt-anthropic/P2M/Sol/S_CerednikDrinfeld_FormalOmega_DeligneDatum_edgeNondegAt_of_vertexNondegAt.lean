import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_of_vertexNondegAt

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (M' M : FullLattice 𝒪 K)
    (hle : M'.1 ≤ M.1) (hπM : ∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1)
    (hV : d.VertexNondegAt π 𝔭 M) :
    d.EdgeNondegAt π 𝔭 M' M := by
  refine ⟨hle, hπM, ?_, ?_⟩
  · intro v hv
    refine hV v ?_
    rintro ⟨w, hw⟩
    exact hv (hw ▸ hπM w)
  · intro v' hv' hmem

    have hpush : inclBaseChange B hle ((1 : B) ⊗ₜ[𝒪] v') ∈
        d.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
      rw [← hyz, map_add]
      refine Submodule.mem_sup.mpr ⟨inclBaseChange B hle y, d.mono hle (Submodule.mem_map_of_mem hy),
        inclBaseChange B hle z, ?_, rfl⟩
      refine Submodule.smul_induction_on (p := fun z => inclBaseChange B hle z ∈ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) hz
        (fun r hr n _ => ?_) (fun x y hx hy => ?_)
      · show inclBaseChange B hle (r • n) ∈ _
        rw [LinearMap.map_smul]; exact Submodule.smul_mem_smul hr Submodule.mem_top
      · show inclBaseChange B hle (x + y) ∈ _
        rw [LinearMap.map_add]; exact Submodule.add_mem _ hx hy
    have hincl : inclBaseChange B hle ((1 : B) ⊗ₜ[𝒪] v') = (1 : B) ⊗ₜ[𝒪] (⟨(v' : Fin 2 → K), hle v'.2⟩ : ↥M.1) := by
      rfl
    rw [hincl] at hpush
    exact hV ⟨(v' : Fin 2 → K), hle v'.2⟩ hv' hpush
