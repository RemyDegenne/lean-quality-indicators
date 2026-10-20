@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

universe v₁ v₂ v₃ u₁ u₂ u₃

@[inherit_doc Equivalence]
infixr:10 " ≌ " => Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Equivalence

/-- The counit of an equivalence of categories. -/
@[to_dual counitInv /-- The inverse of the counit of an equivalence of categories. -/]
abbrev counit (e : C ≌ D) : e.inverse ⋙ e.functor ⟶ 𝟭 D :=
  e.counitIso.hom

end Equivalence
end CategoryTheory
end
