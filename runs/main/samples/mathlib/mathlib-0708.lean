public section

open Function Set

universe u v

variable {α R M M₂ : Type*}

namespace Set

section SMulWithZero

variable [Zero R] [Zero M] [SMulWithZero R M]

lemma indicator_smul_const (s : Set α) (r : α → R) (m : M) :
    indicator s (r · • m) = (indicator s r · • m) :=
  funext <| indicator_smul_const_apply _ _ _

end SMulWithZero
end Set
end
