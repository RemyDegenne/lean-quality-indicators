public section

open Filter Set Topology

namespace Flow

variable {α : Type*} [TopologicalSpace α]

variable [T1Space α] {φ : _root_.Flow ℝ α} {q x : α}

theorem orbit_injective_of_mem_stableSet_of_ne
    (hx : x ∈ stableSet φ q) (hxq : x ≠ q) :
    Function.Injective (fun t : ℝ => φ t x) := by
  intro t u htu
  by_contra hne
  have hper : Function.Periodic (fun v => φ v x) (t - u) := by
    intro v
    calc
      φ (v + (t - u)) x = φ (v - u) (φ t x) := by
        rw [← φ.map_add]
        congr 1
        ring
      _ = φ (v - u) (φ u x) := congrArg (φ (v - u)) htu
      _ = φ v x := by rw [← φ.map_add, sub_add_cancel]
  exact hxq (eq_of_mem_stableSet_of_periodic hx (sub_ne_zero.mpr hne) hper)

end Flow
end
