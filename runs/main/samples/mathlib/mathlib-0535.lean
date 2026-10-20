@[expose] public section

noncomputable section

namespace CategoryTheory

universe v u v₁ u₁ v₂ u₂

variable (C : Type u) [Category.{v} C]

namespace Grpd

open FreeGroupoid

@[simp]
lemma free_map {C D : Cat.{u, u}} (F : C ⟶ D) : free.map F = map F.toFunctor :=
  rfl

end Grpd
end CategoryTheory
end
end
