@[expose] public section

open Function

universe u u' u'' v

variable {S : Type u'} {T : Type u''} {R : Type u} {M : Type v}

namespace SubMulAction

section AddCommGroup

variable [Ring R] [AddCommGroup M]

variable [Module R M]

variable (p : SubMulAction R M)

variable {x : M}

@[simp, norm_cast]
theorem val_neg (x : p) : ((-x : p) : M) = -x :=
  rfl

end AddCommGroup
end SubMulAction
end
