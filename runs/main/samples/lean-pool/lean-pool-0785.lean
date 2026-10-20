@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace PolygonalCircle

namespace ProperChord

variable {J : PolygonalCircle} (C : J.ProperChord)

theorem chord_inter_firstEdge {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    segment ℝ C.Q C.P ∩ J.edgeSegment 0 = {C.P} := by
  let : Fact (1 < J.n) := ⟨by omega⟩
  have hQnot : C.Q ∉ J.edgeSegment 0 := by
    rw [← hQ]
    intro hmem
    rcases (J.vertex_mem_edgeSegment_iff (k : ZMod J.n) 0).mp hmem with h | h
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (by omega : k < J.n), ZMod.val_zero] at hv
      omega
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (by omega : k < J.n), ZMod.val_add,
        ZMod.val_zero, ZMod.val_one, Nat.zero_add,
        Nat.mod_eq_of_lt (by omega : 1 < J.n)] at hv
      omega
  have hPmem : C.P ∈ J.edgeSegment 0 := by
    rw [← hP]
    exact left_mem_segment ℝ _ _
  apply Set.Subset.antisymm
  · rintro x ⟨hxChord, hxEdge⟩
    have hxCarrier : x ∈ J.carrier := J.edgeSegment_subset_carrier _ hxEdge
    have hx : x ∈ segment ℝ C.P C.Q ∩ J.carrier := by
      rw [segment_symm]
      exact ⟨hxChord, hxCarrier⟩
    rw [C.segment_inter_carrier] at hx
    rcases hx with rfl | rfl
    · exact Set.mem_singleton _
    · exact (hQnot hxEdge).elim
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨right_mem_segment ℝ _ _, hPmem⟩

end ProperChord
end PolygonalCircle
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
