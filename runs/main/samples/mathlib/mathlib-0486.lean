@[expose] public section

set_option linter.style.longFile 1600

open Function Fintype Nat Pointwise Subgroup Submonoid

open scoped Finset

variable {G H A α β : Type*}

section FiniteGroup

variable [Group G] {x y : G}

variable [Fintype G] {x : G} {n : ℕ}

open QuotientGroup

@[to_additive]
theorem image_range_orderOf [DecidableEq G] :
    letI : Fintype (zpowers x) := (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
    Finset.image (fun i => x ^ i) (Finset.range (orderOf x)) = (zpowers x : Set G).toFinset := by
  let : Fintype (zpowers x) := (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
  ext x
  rw [Set.mem_toFinset, SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf]

end FiniteGroup
end
