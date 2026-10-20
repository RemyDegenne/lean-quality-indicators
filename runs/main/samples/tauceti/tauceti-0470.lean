public section

namespace TauCeti.Huber.Pair.Hom

open Topology TauCeti.ValuationSpectrum

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B] {S : Pair A} {T : Pair B}

theorem exists_mem_spaRationalFamily_spaComap_preimage_eq_of_denseRange (f : Hom S T)
    (hf : DenseRange f.toRingHom) {U : Set (spa T.plus)} (hU : U ∈ spaRationalFamily T.plus) :
    ∃ W ∈ spaRationalFamily S.plus, f.spaComap ⁻¹' W = U := by
  rw [spaComap_def]
  exact ValuationSpectrum.exists_mem_spaRationalFamily_spaComap_preimage_eq_of_denseRange
    f.continuous_toRingHom hf S.plus T.plus f.map_mem_plus hU

end TauCeti.Huber.Pair.Hom
end
