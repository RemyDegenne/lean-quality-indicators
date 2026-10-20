public section

namespace TauCeti.ValuationSpectrum

open Topology _root_.TopologicalSpace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] {ι : Type*}

theorem mem_laurentPiece_setOf_vle {Aplus : Subring A} {v : Spv A} (hv : v ∈ spa Aplus)
    (f : ι → A) : v ∈ laurentPiece Aplus f {i | v.toValuativeRel.vle 1 (f i)} :=
  ⟨hv, fun i ↦ ⟨id, fun hi ↦ (v.toValuativeRel.vle_total (f i) 1).resolve_right hi⟩⟩

end TauCeti.ValuationSpectrum
end
