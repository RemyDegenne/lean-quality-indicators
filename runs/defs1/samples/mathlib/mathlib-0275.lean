@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed

section Sections

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

variable (I : C) [Closed I]

variable {I}

namespace Over

open ChosenPullbacksAlong

variable (I) [ChosenPullbacksAlong (curryRightUnitorHom I)]

variable {I}

open ChosenPullbacksAlong

variable [BraidedCategory C]

open Adjunction

variable (I)

set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary definition which is used to define the adjunction between the star functor
and the sections functor. See `starSectionsAdjunction`. -/
@[simps homEquiv]
def coreHomEquivToOverSections : CoreHomEquiv (toOver I) (sections I) where
  homEquiv A X :=
    { toFun := sectionsCurry
      invFun := sectionsUncurry
      left_inv {u} := sectionsUncurry_sectionsCurry
      right_inv {v} := sectionsCurry_sectionUncurry }
  homEquiv_naturality_left_symm := by
    intro A' A X g v
    dsimp [sectionsCurry, sectionsUncurry, curryRightUnitorHom]
    simp only [toOver_map]
    rw [← Over.homMk_comp]
    congr 1
    simp [uncurry_natural_left]
  homEquiv_naturality_right := by
    intro A X' X u g
    dsimp [sectionsCurry, sectionsUncurry, curryRightUnitorHom]
    apply ChosenPullbacksAlong.hom_ext
    · simp [← curry_natural_right]
    · simp

end Over
end Sections
end CategoryTheory
end
