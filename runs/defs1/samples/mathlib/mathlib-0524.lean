@[expose] public section

section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v v₂ u u₂

open WalkingParallelPair

open WalkingParallelPairHom

variable {C : Type u}

variable {X Y : C}

variable [Category.{v} C]

variable {f g : X ⟶ Y}

/--
If `f, g : X ⟶ Y` and `f', g : X' ⟶ Y'` pairwise form a commutative square with isomorphisms
`X ≅ X'` and `Y ≅ Y'`, the categories of forks are equivalent.
-/
def Fork.equivOfIsos {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
    {f' g' : X' ⟶ Y'} (e₀ : X ≅ X') (e₁ : Y ≅ Y')
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch) :
    Fork f g ≌ Fork f' g' :=
  Cone.postcomposeEquivalence <|
    parallelPair.ext e₀ e₁ (by simp [comm₁]) (by simp [comm₂])

end CategoryTheory.Limits
end
end
