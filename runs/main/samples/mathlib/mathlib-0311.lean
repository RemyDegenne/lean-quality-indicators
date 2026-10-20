@[expose] public section

namespace Unitization

section Basic

variable {R A : Type*}

lemma mk_toProd (x : Unitization R A) : mk x.toProd = x := rfl

end Basic
end Unitization
end
