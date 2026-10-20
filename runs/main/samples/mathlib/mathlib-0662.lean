@[expose] public section

noncomputable section

universe u v w

open Function Set

open scoped Uniformity

namespace Metric

namespace Sigma

variable {ι : Type*} {E : ι → Type*} [∀ i, MetricSpace (E i)]

attribute [local instance] Sigma.instDist

protected theorem dist_triangle (x y z : Σ i, E i) : dist x z ≤ dist x y + dist y z := by
  rcases x with ⟨i, x⟩; rcases y with ⟨j, y⟩; rcases z with ⟨k, z⟩
  rcases eq_or_ne i k with (rfl | hik)
  · rcases eq_or_ne i j with (rfl | hij)
    · simpa using dist_triangle x y z
    · simp only [Sigma.dist_same, Sigma.dist_ne hij, Sigma.dist_ne hij.symm]
      calc
        dist x z ≤ dist x (Nonempty.some ⟨x⟩) + 0 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
          simpa only [zero_add, add_zero] using dist_triangle _ _ _
        _ ≤ _ := by apply_rules [add_le_add, le_rfl, dist_nonneg, zero_le_one]
  · rcases eq_or_ne i j with (rfl | hij)
    · simp only [Sigma.dist_ne hik, Sigma.dist_same]
      calc
        dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z ≤
            dist x y + dist y (Nonempty.some ⟨y⟩) + 1 + dist (Nonempty.some ⟨z⟩) z := by
          apply_rules [add_le_add, le_rfl, dist_triangle]
        _ = _ := by abel
    · rcases eq_or_ne j k with (rfl | hjk)
      · simp only [Sigma.dist_ne hij, Sigma.dist_same]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z ≤
              dist x (Nonempty.some ⟨x⟩) + 1 + (dist (Nonempty.some ⟨z⟩) y + dist y z) := by
            apply_rules [add_le_add, le_rfl, dist_triangle]
          _ = _ := by abel
      · simp only [hik, hij, hjk, Sigma.dist_ne, Ne, not_false_iff]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z =
              dist x (Nonempty.some ⟨x⟩) + 1 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
            simp only [add_zero, zero_add]
          _ ≤ _ := by apply_rules [add_le_add, zero_le_one, dist_nonneg, le_rfl]

end Sigma
end Metric
end
end
