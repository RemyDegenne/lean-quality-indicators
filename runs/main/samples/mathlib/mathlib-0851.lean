@[expose] public section

open Function hiding comp

universe u v w

namespace ApplicativeTransformation

variable (F : Type u → Type v) [Applicative F]

variable (G : Type u → Type w) [Applicative G]

variable {F G}

protected theorem congr_arg (η : ApplicativeTransformation F G) {α : Type u} {x y : F α}
    (h : x = y) : η x = η y :=
  congrArg (fun z : F α => η z) h

end ApplicativeTransformation
end
