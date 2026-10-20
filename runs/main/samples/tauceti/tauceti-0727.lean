public section

noncomputable section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy

variable {N : Type*}

variable [Fintype N]

theorem cubeRadius_eq_one_iff (z : I^N) : cubeRadius z = 1 ↔ z ∈ Cube.boundary N := by
  constructor
  · intro h
    by_contra hz
    simp only [Cube.boundary, Set.mem_ofPred_eq, not_exists, not_or] at hz
    have hlt : dist z (cubeCenter : I^N) < 1 / 2 := by
      rw [dist_pi_lt_iff (by norm_num)]
      intro i
      rw [dist_apply_cubeCenter, abs_lt]
      have h0 := (z i).2.1
      have h1 := (z i).2.2
      have e0 : (z i : ℝ) ≠ 0 := fun hc => (hz i).1 (Subtype.ext hc)
      have e1 : (z i : ℝ) ≠ 1 := fun hc => (hz i).2 (Subtype.ext hc)
      constructor <;> [rcases h0.lt_or_eq with h | h; rcases h1.lt_or_eq with h | h] <;>
        first
          | linarith
          | exact absurd h.symm e0
          | exact absurd h e1
    rw [cubeRadius_def] at h
    linarith
  · rintro ⟨i, hi⟩
    refine le_antisymm (cubeRadius_le_one z) ?_
    have h_one : (1 : ℝ) = 2 * (1 / 2) := by norm_num
    rw [cubeRadius_def, h_one]
    gcongr
    refine le_trans ?_ (dist_le_pi_dist z (cubeCenter : I^N) i)
    rw [dist_apply_cubeCenter]
    rcases hi with hi | hi <;> rw [hi] <;> norm_num

end TauCeti
end
end
