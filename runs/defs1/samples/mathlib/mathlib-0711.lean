@[expose] public section

universe w v u

namespace CategoryTheory.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- In a bicategory, `eqToHom`s do not compose strictly,
but they do up to isomorphism. -/
def eqToHomTransIso {x y z : B} (e₁ : x = y) (e₂ : y = z) :
    eqToHom (e₁.trans e₂) ≅ eqToHom e₁ ≫ eqToHom e₂ :=
  e₂ ▸ e₁ ▸ (λ_ (𝟙 x)).symm

end CategoryTheory.Bicategory
end
