@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

section BaseChange

variable {D : Type u}

/-- The underlying morphism of a module-level section, in raw
tensor form. -/
def baseChangeSectionHom
    [Category.{v} D] [MonoidalCategory D] [Abelian D] (R : D) [MonObj R]
    {S : CategoryTheory.ShortComplex D}
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂) :
    R ⊗ S.X₃ ⟶ R ⊗ S.X₂ :=
  Mod.Hom.hom s

end BaseChange
end RS
end
