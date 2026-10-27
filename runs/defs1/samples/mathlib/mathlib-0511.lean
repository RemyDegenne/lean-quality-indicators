@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

open Opposite

section Prod

section

variable {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
  (S : C ⥤ D) (S' : C' ⥤ D') (T : D) (T' : D')

/-- Implementation; see `CostructuredArrow.prodEquivalence`. -/
@[simps]
def CostructuredArrow.prodFunctor :
    CostructuredArrow (S.prod S') (T, T') ⥤ CostructuredArrow S T × CostructuredArrow S' T' where
  obj f := ⟨.mk f.hom.1, .mk f.hom.2⟩
  map η := ⟨CostructuredArrow.homMk η.left.1 (by simp),
            CostructuredArrow.homMk η.left.2 (by simp)⟩

end
end Prod
end CategoryTheory
end
