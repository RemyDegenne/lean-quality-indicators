@[expose] public section

open CategoryTheory

open Convexity TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

open CategoryTheory Convexity TopologicalSpace

open scoped Simplicial

noncomputable section

namespace AlgebraicTopology

/-- The integer-linear boundary from degree `n + 1` to degree `n`, sending a
simplex to the alternating face sum with coefficient `(-1)^i` on its `i`th face. -/
def sSetFinsuppBoundary (Z : SSet.{u}) (n : ℕ) :
    (Z _⦋n + 1⦌ →₀ ℤ) →ₗ[ℤ] (Z _⦋n⦌ →₀ ℤ) :=
  Finsupp.lift (Z _⦋n⦌ →₀ ℤ) ℤ (Z _⦋n + 1⦌)
    (fun x ↦ ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • Finsupp.single (Z.δ i x) 1)

end AlgebraicTopology
end
end
end
