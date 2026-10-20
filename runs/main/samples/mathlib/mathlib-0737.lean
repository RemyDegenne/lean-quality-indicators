@[expose] public section

set_option linter.style.longFile 1600

open Function Fintype Nat Pointwise Subgroup Submonoid

open scoped Finset

variable {G H A α β : Type*}

section FiniteGroup

variable [Group G] {x y : G}

section Finite

variable [Finite G]

@[to_additive
]
lemma Subgroup.closure_toSubmonoid_of_finite {s : Set G} :
    (closure s).toSubmonoid = Submonoid.closure s :=
  closure_toSubmonoid_of_isOfFinOrder <| by simp [isOfFinOrder_of_finite]

end Finite
end FiniteGroup
end
