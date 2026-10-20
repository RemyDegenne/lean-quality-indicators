public section

open Filter Set Topology

namespace Flow

variable {α : Type*} [TopologicalSpace α]

variable [T1Space α] {φ : _root_.Flow ℝ α} {q x : α}

theorem eq_of_mem_stableSet_of_periodic (hx : x ∈ stableSet φ q) {T : ℝ}
    (hT : T ≠ 0) (hper : Function.Periodic (fun t => φ t x) T) : x = q := by
  have hpos : ∃ T' : ℝ, 0 < T' ∧ Function.Periodic (fun t => φ t x) T' := by
    rcases lt_trichotomy T 0 with hneg | heq | hpositive
    · exact ⟨-T, neg_pos.mpr hneg, hper.neg⟩
    · exact (hT heq).elim
    · exact ⟨T, hpositive, hper⟩
  obtain ⟨T', hT', hper'⟩ := hpos
  have htend : Tendsto (fun n : ℕ => n • T') atTop atTop :=
    tendsto_id.atTop_nsmul_const hT'
  have hlim : Tendsto (fun n : ℕ => φ (n • T') x) atTop (𝓝 q) :=
    (mem_stableSet.mp hx).comp htend
  have hconst : (fun n : ℕ => φ (n • T') x) = fun _ => x := by
    funext n
    simpa only [φ.map_zero_apply] using (hper'.nsmul_eq n)
  have hlim' : Tendsto (fun _ : ℕ => x) atTop (𝓝 q) := by
    simpa only [hconst] using hlim
  exact tendsto_const_nhds_iff.mp hlim'

end Flow
end
