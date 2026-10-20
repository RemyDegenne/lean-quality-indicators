open scoped Finset

@[expose] public section

open scoped Pointwise

variable {M N : Type*} [Monoid M]

variable {G H : Type*} [Group G] [AddGroup H]

section Group

variable (G H)

variable {G H}

theorem GroupFG.iff_add_fg : Group.FG G ↔ AddGroup.FG (Additive G) :=
  isAddFG_additive_iff.symm

end Group
end
