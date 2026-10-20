@[expose] public section

universe u v w u₁

namespace DirectSum

open DirectSum Finsupp Module

section Congr

variable {R : Type*} [Semiring R]
    {ι : Type*}
    {N : ι → Type*} [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module R (N i)]
    {P : ι → Type*} [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]

/-- Direct sums of isomorphic modules are isomorphic. -/
def congrLinearEquiv (u : (i : ι) → N i ≃ₗ[R] P i) :
    (⨁ i, N i) ≃ₗ[R] ⨁ i, P i where
  toAddEquiv := congrAddEquiv (fun i ↦ (u i).toAddEquiv)
  map_smul' r x := by
    exact (DirectSum.lmap (fun i ↦ (u i).toLinearMap)).map_smul r x

end Congr
end DirectSum
end
