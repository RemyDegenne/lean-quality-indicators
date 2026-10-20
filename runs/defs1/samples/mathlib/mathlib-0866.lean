@[expose] public section

variable {X Y Z α : Type*} [TopologicalSpace X]

open Set Filter

open scoped Topology

namespace LocallyConstant

section Equiv

/--
The equivalence between `LocallyConstant X Y` and `LocallyConstant X Z` given an
equivalence `Y ≃ Z`
-/
@[simps]
def congrRight (e : Y ≃ Z) : LocallyConstant X Y ≃ LocallyConstant X Z where
  toFun := map e
  invFun := map e.symm
  left_inv := by intro; ext; simp
  right_inv := by intro; ext; simp

end Equiv
end LocallyConstant
end
