@[expose] public section

universe a w p r v

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

@[simp]
theorem normalizedIntegralSimplex_of_mem_nonDegenerate (S : SSet.{w}) {n : ℕ}
    (s : S _⦋n⦌) (hs : s ∈ S.nonDegenerate n) :
    S.normalizedIntegralSimplex s = Finsupp.single ⟨s, hs⟩ 1 := by
  classical
  simp [normalizedIntegralSimplex, hs]

end SSet
end
