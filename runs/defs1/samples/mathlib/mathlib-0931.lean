@[expose] public section

namespace CategoryTheory.Oplax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : B ⥤ᵒᵖᴸ C}

namespace LaxTrans

open scoped Oplax.LaxTrans

variable (η θ : F ⟶ G)

variable {η θ}

namespace Modification

/-- Vertical composition of modifications. -/
@[simps]
def vcomp {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι) : Modification η ι where
  app a := Γ.app a ≫ Δ.app a

end Modification
end LaxTrans
end CategoryTheory.Oplax
end
