@[expose] public section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

namespace LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

variable {s t : LeftExtension f g}

/-- The left extension along the identity. -/
def alongId (g : a ⟶ c) : LeftExtension (𝟙 a) g := .mk _ (λ_ g).inv

end LeftExtension
end Bicategory
end CategoryTheory
end
