@[expose] public section

universe a w p r v

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

@[simp]
theorem normalizedIntegralBoundary_single (S : SSet.{w}) (n : ℕ)
    (s : S.nonDegenerate (n + 1)) :
    S.normalizedIntegralBoundary n (Finsupp.single s 1) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • S.normalizedIntegralSimplex (S.δ i s.val) := by
  classical
  simp [normalizedIntegralBoundary, Finsupp.lift_apply]

end SSet
end
