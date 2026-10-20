@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace PolygonalCircle

namespace ProperChord

variable {J : PolygonalCircle} (C : J.ProperChord)

open scoped Classical in
theorem crossingCount_forwardCutCircle {k : ℕ} (hk2 : 2 ≤ k)
    (hk : k + 1 < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) (P : Plane) :
    (C.forwardCutCircle hk2 hk hP hQ).crossingCount P =
      (∑ m ∈ Finset.range k, if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0) +
        if SegmentCrossed C.P C.Q P then 1 else 0 := by
  unfold crossingCount
  change (∑ m ∈ Finset.range (k + 1),
    if (C.forwardCutCircle hk2 hk hP hQ).EdgeCrossed (m : ZMod (k + 1)) P
      then 1 else 0) = _
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    have hmlt := Finset.mem_range.mp hm
    rw [C.forwardCutCircle_edgeCrossed_of_lt hk2 hk hP hQ hmlt]
  · rw [C.forwardCutCircle_edgeCrossed_last hk2 hk hP hQ]

end ProperChord
end PolygonalCircle
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
