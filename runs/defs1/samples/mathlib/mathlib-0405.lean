@[expose] public section

open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

@[inherit_doc]
infixl:25 " ≃ " => Equiv

namespace Equiv

/-- The `Sort` of proofs of a true proposition is equivalent to `PUnit`. -/
def propEquivPUnit {p : Prop} (h : p) : p ≃ PUnit.{0} := @equivPUnit p <| uniqueProp h

end Equiv
end
