public section

open NNReal

variable {ι ι' E F : Type*} {G : ι → Type*}

section AdditiveMultiplicative

open Additive Multiplicative

section Norm

variable [Norm E]

@[simp] lemma norm_toMul (x : Additive E) : ‖(x.toMul : E)‖ = ‖x‖ := rfl

end Norm
end AdditiveMultiplicative
end
