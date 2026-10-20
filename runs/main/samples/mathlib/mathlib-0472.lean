@[expose] public section

namespace WithConv

variable {R A B C : Type*}

variable [AddCommMonoid A]

@[simp] lemma linearEquiv_apply [Semiring R] [Module R A]
    (a : WithConv A) : WithConv.linearEquiv R A a = ofConv a := rfl

end WithConv
end
