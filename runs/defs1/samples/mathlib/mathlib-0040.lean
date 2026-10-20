@[expose] public section

open scoped Pointwise

open MulAction Function

namespace SubMulAction

variable (M : Type*) {α : Type*} [Group M] [MulAction M α] (s : Set α)

variable {s}

variable {M}

section Comparisons

variable {s t : Set α}

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/-- The equivariant map between `SubMulAction.ofStabilizer M a`
and `ofFixingSubgroup M {a}`. -/
@[to_additive /-- The equivariant map between `SubAddAction.ofStabilizer M a`
and `ofFixingAddSubgroup M {a}`. -/]
def ofFixingSubgroup_of_singleton (a : α) :
    let φ : fixingSubgroup M ({a} : Set α) → stabilizer M a := fun ⟨m, hm⟩ =>
      ⟨m, ((mem_fixingSubgroup_iff M).mp hm) a (Set.mem_singleton a)⟩
    ofFixingSubgroup M ({a} : Set α) →ₑ[φ] ofStabilizer M a where
  toFun x := ⟨x, by simp⟩
  map_smul' _ _ := rfl

end Comparisons
end SubMulAction
end
