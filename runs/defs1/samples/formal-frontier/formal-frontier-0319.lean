@[expose] public section

universe a w p r v

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

/-- The alternating boundary on nondegenerate integral generators.
The zeroth face has positive sign; degenerate faces contribute zero. -/
noncomputable def normalizedIntegralBoundary (S : SSet.{w}) (n : ℕ) :
    (S.nonDegenerate (n + 1) →₀ ℤ) →ₗ[ℤ] (S.nonDegenerate n →₀ ℤ) :=
  Finsupp.lift _ ℤ _ fun s ↦
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • S.normalizedIntegralSimplex (S.δ i s.val)

end SSet
end
