@[expose] public section

open Function MulOpposite

open scoped Pointwise

variable {F α β γ : Type*}

namespace Set

scoped[Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet Set.mulAction Set.addAction

section Group

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

@[to_additive]
theorem preimage_smul (a : α) (t : Set β) : (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t :=
  ((MulAction.toPerm a).image_symm_eq_preimage _).symm

end Group
end Set
end
