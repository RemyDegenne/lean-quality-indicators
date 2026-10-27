@[expose] public section

universe u v

namespace WType

section List

variable (γ : Type u)

/-- The arities of each constructor for lists, `nil` takes no arguments, `cons hd` takes one -/
def Listβ : Listα γ → Type u
  | Listα.nil => PEmpty
  | Listα.cons _ => PUnit

end List
end WType
end
