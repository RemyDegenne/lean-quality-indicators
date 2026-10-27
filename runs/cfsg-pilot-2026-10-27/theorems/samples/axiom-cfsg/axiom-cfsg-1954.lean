public section

namespace CFSG.HardMathSupport.C14Idx

open scoped Function

theorem range_image_iterate_stable {X : Type*} [DecidableEq X] {θ : X → X} {α : X} {n : ℕ}
    (hn : 0 < n) (hnα : (θ)^[n] α = α) :
    ∀ β ∈ (Finset.range n).image (fun i => (θ)^[i] α), θ β ∈
      (Finset.range n).image fun i => (θ)^[i] α := by
  intro β hβ
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hβ
  have hi' : i < n := Finset.mem_range.1 hi
  by_cases hlt : i + 1 < n
  · simpa [Function.iterate_succ_apply'] using mem_range_image_iterate (θ := θ) (α := α) hlt
  · have hile : i.succ = n := by omega
    have heq : θ ((θ)^[i] α) = (θ)^[n] α := by
      rw [← Function.iterate_succ_apply' (θ) i α, hile]
    rw [heq, hnα]
    exact mem_range_image_iterate (θ := θ) (α := α) hn

end CFSG.HardMathSupport.C14Idx
end
