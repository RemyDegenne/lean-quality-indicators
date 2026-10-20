public section

namespace TauCeti

open Equiv Equiv.Perm

variable {α σ : Type*}

@[simp]
theorem invariantColouringEquiv_symm_apply (π : Perm α)
    (f : {f : α → σ // f ∘ π = f}) (a : α) :
    (invariantColouringEquiv π).symm f (Quotient.mk _ a) = f.1 a :=
  congrFun (congrArg Subtype.val ((invariantColouringEquiv π).apply_symm_apply f)) a

end TauCeti
end
