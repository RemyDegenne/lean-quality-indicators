public section

namespace CFSG.RankTwoShapes

open scoped Pointwise

variable {G : Type*} [Group G]

namespace AlperinDecomposition

variable {p : ℕ} {S : Subgroup G}

theorem exists_moving_step {P : Subgroup G} {c x : G} (h : AlperinDecomposition p S P c)
    (hx : x ∈ P) (hcx : c⁻¹ * x * c ≠ x) :
    ∃ Q : Subgroup G, IsAlperinSubgroup p S Q ∧ x ∈ Q ∧
      ∃ n ∈ (Subgroup.normalizer (Q : Set G)), n⁻¹ * x * n ≠ x := by
  induction h with
  | one => exact absurd (by group) hcx
  | @step c n Q _ hQ hPQ hn ih =>
      by_cases hcx' : c⁻¹ * x * c = x
      · refine ⟨Q, hQ, ?_, n, hn, ?_⟩
        · have hmem := conj_mem_map_conj_inv c hx
          rw [hcx'] at hmem
          exact hPQ hmem
        · intro hnx
          apply hcx
          calc (c * n)⁻¹ * x * (c * n) = n⁻¹ * (c⁻¹ * x * c) * n := by group
            _ = x := by rw [hcx', hnx]
      · exact ih hcx'

end AlperinDecomposition
end CFSG.RankTwoShapes
end
