public section

open Bornology Complex Filter Metric Set Topology

namespace TauCeti

theorem IsJordanCurve.mem_filledHull_iff_notMem_filledHull_of_locally_eq_line {C : Set ℂ}
    (hC : IsJordanCurve C) {p v a b : ℂ} {r : ℝ}
    (hline : ∀ z ∈ ball p r, z ∈ C ↔ (v * (z - p)).im = 0)
    (ha : a ∈ ball p r) (hb : b ∈ ball p r)
    (ha' : 0 < (v * (a - p)).im) (hb' : (v * (b - p)).im < 0) :
    a ∈ filledHull C ↔ b ∉ filledHull C := by
  have hab := hC.notMem_connectedComponentIn_of_locally_eq_line hline ha hb ha' hb'
  refine ⟨fun haH hbH => hab ?_, fun hbH => ?_⟩
  · have haC : a ∉ C := fun h => ha'.ne' ((hline a ha).mp h)
    have hbC : b ∉ C := fun h => hb'.ne ((hline b hb).mp h)
    rw [← hC.filledHull_sdiff_eq_connectedComponentIn_of_locally_eq_line (pos_of_mem_ball ha) v
      hline ⟨haH, haC⟩]
    exact ⟨hbH, hbC⟩
  · have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      exact Cardinal.one_lt_two
    exact (mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn hrank
      hC.isCompact.isBounded hab).resolve_right hbH

end TauCeti
end
