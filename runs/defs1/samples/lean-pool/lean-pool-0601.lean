@[expose] public section

universe u

variable {A B C : Type*}

namespace Rose

/-- Applies a function to every label in a `Rose` tree. -/
def map (f : A → B) : Rose A → Rose B :=
  bind (fun x ↦ ⟨f x, []⟩)

end Rose
end
