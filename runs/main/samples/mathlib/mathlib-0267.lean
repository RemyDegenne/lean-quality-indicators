@[expose] public section

export Btw (btw)

export SBtw (sbtw)

export CircularPreorder (btw_refl btw_cyclic_left sbtw_trans_left)

export CircularPartialOrder (btw_antisymm)

export CircularOrder (btw_total)

section CircularPartialOrder

variable {α : Type*} [CircularPartialOrder α]

theorem Btw.btw.antisymm {a b c : α} (h : btw a b c) : btw c b a → a = b ∨ b = c ∨ c = a :=
  btw_antisymm h

end CircularPartialOrder
end
