@[expose] public section

universe w' w v₁ v₂ u₁ u₂

open CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

open ConcreteCategory

section ZeroMorphisms

variable [HasZeroMorphisms C]

theorem isCoseparator_prod_of_isCoseparator_left (G H : C) [HasBinaryProduct G H]
    (hG : IsCoseparator G) : IsCoseparator (G ⨯ H) :=
  (isCoseparator_prod _ _).2 <| ObjectProperty.IsCoseparating.of_le hG <| by simp

end ZeroMorphisms
end CategoryTheory
end
