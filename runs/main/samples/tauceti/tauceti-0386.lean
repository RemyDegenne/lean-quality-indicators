public section

open Topology

namespace TauCeti.Huber.Pair.Hom

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  {S : Pair A} {T : Pair B} {U : Pair C}

theorem IsQuotientMapping.mem_plus_iff {f : Hom S T} (hf : IsQuotientMapping f) {b : B} :
    b ∈ T.plus ↔ IsIntegral (S.plus.map f.toRingHom) b := by
  rw [hf.plus_eq, Subalgebra.mem_toSubring, mem_integralClosure_iff]

end TauCeti.Huber.Pair.Hom
end
