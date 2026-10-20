@[expose] public section

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

open MonoidalCategory Limits

namespace CartesianMonoidalCategory

export SemiCartesianMonoidalCategory (isTerminalTensorUnit fst snd fst_def snd_def toUnit
  toUnit_unique toUnit_unit comp_toUnit comp_toUnit_assoc default_eq_toUnit)

variable {C : Type u} [Category.{v} C]

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open MonoidalCategory

section CartesianMonoidalCategoryComparison

variable {D : Type u₁} [Category.{v₁} D] [CartesianMonoidalCategory D] (F : C ⥤ D)

variable {E : Type u₂} [Category.{v₂} E] [CartesianMonoidalCategory E] (G : D ⥤ E)

section prodComparison

variable (A B : C)

variable {A B} {A' B' : C}

variable {E : Type u₂} [Category.{v₂} E] [CartesianMonoidalCategory E] (G : D ⥤ E)

open Limits

section PreservesLimitPairs

section

variable (A B)

variable [PreservesLimit (pair A B) F]

/-- If `F` preserves the limit of the pair `(A, B)`, then `prodComparison F A B` is an isomorphism.
-/
noncomputable def prodComparisonIso : F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B :=
  IsLimit.conePointUniqueUpToIso (isLimitCartesianMonoidalCategoryOfPreservesLimits F A B)
    (tensorProductIsBinaryProduct _ _)

end
end PreservesLimitPairs
end prodComparison
end CartesianMonoidalCategoryComparison
end CartesianMonoidalCategory
end CategoryTheory
end
