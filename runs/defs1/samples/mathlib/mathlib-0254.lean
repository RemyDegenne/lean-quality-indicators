@[expose] public section

universe u v

open CategoryTheory

attribute [instance] SemiRingCat.semiring

namespace SemiRingCat

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (R S : SemiRingCat) (f : Hom R S) :=
  f.hom

end SemiRingCat
end
