namespace OAI

section

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp

namespace SimpleAmenable.SymmetricConfiguration

attribute [local instance 1200] Rep.hV2

variable {m p:ℕ}

@[simp] theorem listEquiv_apply_val (f : Configuration m p) :
    (listEquiv m p f).val=List.ofFn f.val := rfl

end SimpleAmenable.SymmetricConfiguration
end
end OAI
