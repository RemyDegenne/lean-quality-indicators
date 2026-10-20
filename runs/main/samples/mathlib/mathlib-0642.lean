@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

section

variable (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)

@[to_dual
]
theorem splitEpiCategoryImpOfIsEquivalence [IsEquivalence F] [SplitEpiCategory C] :
    SplitEpiCategory D :=
  ⟨fun {X} {Y} f => by
    intro
    rw [← F.inv.isSplitEpi_iff f]
    apply isSplitEpi_of_epi⟩

end
end CategoryTheory.Functor
end
