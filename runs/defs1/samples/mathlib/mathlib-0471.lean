@[expose] public section

universe v₁ u₁ v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace GrothendieckTopology

variable {C}

variable {X Y : C} {S R : Sieve X}

variable (J : GrothendieckTopology C)

variable (C)

variable {C}

/-- Pull back a cover along a morphism. -/
@[simps obj]
def pullback (f : Y ⟶ X) : J.Cover X ⥤ J.Cover Y where
  obj S := S.pullback f
  map f := (Sieve.pullback_monotone _ f.le).hom

end GrothendieckTopology
end CategoryTheory
end
