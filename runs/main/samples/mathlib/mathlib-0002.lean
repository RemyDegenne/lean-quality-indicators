@[expose] public section

open scoped Pointwise

theorem top_fixedByFinite {K L : Type*} [Field K] [Field L] [Algebra K L] :
    ⊤ ∈ fixedByFinite K L :=
  ⟨⊥, IntermediateField.instFiniteSubtypeMemBot K, IntermediateField.fixingSubgroup_bot⟩

end
