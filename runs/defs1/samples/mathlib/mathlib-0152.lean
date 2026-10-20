@[expose] public section

universe u v

variable {α β : Type*}

open Finset

/-- If the subtype of all-but-one elements is a `Fintype` then the type itself is a `Fintype`. -/
@[instance_reducible]
def fintypeOfFintypeNe (a : α) (_ : Fintype { b // b ≠ a }) : Fintype α :=
  Fintype.ofBijective (Sum.elim ((↑) : { b // b = a } → α) ((↑) : { b // b ≠ a } → α)) <| by
    classical exact (Equiv.sumCompl (· = a)).bijective

end
