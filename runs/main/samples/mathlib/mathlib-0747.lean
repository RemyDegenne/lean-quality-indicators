@[expose] public section

open commutatorElement Subgroup

section WithGroup

variable {G : Type*} [Group G] (N : Subgroup G) [Normal N]

namespace Group

@[to_additive]
lemma IsNilpotent.isVirtuallyNilpotent (hG : IsNilpotent G) : IsVirtuallyNilpotent G :=
  ⟨⊤, by simpa, inferInstance⟩

end Group
end WithGroup
end
