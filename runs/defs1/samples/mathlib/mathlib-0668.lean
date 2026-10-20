@[expose] public section

universe u

open CategoryTheory MonoidalCategory Simplicial SimplicialObject.Truncated
  CartesianMonoidalCategory Limits

namespace SSet

namespace Truncated

namespace HomotopyCategory

namespace BinaryProduct

variable {X X' Y Y' Z : Truncated.{u} 2}

set_option backward.isDefEq.respectTransparency.types false in
variable (X Y) in
/-- The functor `X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
def curriedInverse : X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory :=
  lift (fun x ↦ lift (fun y ↦ mk (x, y)) (fun {y₀ y₁} e ↦ homMk (Edge.tensor (.id _) e)) (by simp)
    (fun {y₀ y₁ y₁ e₀₁ e₁₂ e₀₂ h} ↦ homMk_comp_homMk ((Edge.CompStruct.idCompId x).tensor h)))
    (fun {x₀ x₁} e ↦ mkNatTrans (fun y ↦ homMk (V := X ⊗ Y) (x₀ := (x₀, y))
      (x₁ := (x₁, y)) (e.tensor (.id y))) (fun y₀ y₁ e' ↦ by simp [square]))
    (by cat_disch) (fun {x₀ x₁ x₂ e₀₁ e₁₂ e₀₂} h ↦ by
      ext y
      obtain ⟨y, rfl⟩ := mk_surjective y
      simpa using homMk_comp_homMk (h.tensor (.idCompId y)))

end BinaryProduct
end HomotopyCategory
end Truncated
end SSet
end
