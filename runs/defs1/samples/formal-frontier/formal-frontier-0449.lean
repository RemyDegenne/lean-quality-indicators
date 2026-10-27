@[expose] public section

universe u v

/-- A subspace of a coalgebra over a field closed under comultiplication into the image of
its tensor square. -/
structure Subcoalgebra (K : Type u) (C : Type v)
    [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C] : Type v
    extends Submodule K C where
  /-- Comultiplication of every member lies in the image of the tensor square of the subspace. -/
  comul_mem' : ∀ ⦃x : C⦄, x ∈ toSubmodule →
    Coalgebra.comul (R := K) x ∈
      LinearMap.range (TensorProduct.mapIncl toSubmodule toSubmodule)

end
