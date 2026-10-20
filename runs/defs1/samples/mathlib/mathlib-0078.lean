@[expose] public section

noncomputable section

namespace CategoryTheory.Limits

open CategoryTheory

universe w w' v u u₂

variable {J : Type w}

open WalkingParallelFamily

open WalkingParallelFamily.Hom

attribute [local aesop safe cases] WalkingParallelFamily.Hom

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (f : J → (X ⟶ Y))

variable {f}

variable (f)

section

variable [HasWideEqualizer f]

/-- If a wide equalizer of `f` exists, we can access the inclusion `wideEqualizer f ⟶ X` by
    saying `wideEqualizer.ι f`. -/
abbrev wideEqualizer.ι : wideEqualizer f ⟶ X :=
  limit.π (parallelFamily f) zero

end
end CategoryTheory.Limits
end
end
