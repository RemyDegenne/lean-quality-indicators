@[expose] public section

universe v₁ v₂ u₁ u₂

open Opposite

variable {C : Type u₁}

namespace CategoryTheory

open CategoryTheory.Functor

variable [Category.{v₁} C]

namespace NatTrans

variable {D : Type u₂} [Category.{v₂} D]

section

variable {F G : C ⥤ D}

/-- The opposite of a natural transformation. -/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
protected def op (α : F ⟶ G) : G.op ⟶ F.op where
  app X := (α.app (unop X)).op
  naturality X Y f := Quiver.Hom.unop_inj (by simp)

end
end NatTrans
end CategoryTheory
end
