@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Comonad

open Limits

noncomputable section

open CategoryTheory Adjunction Comonad ComonadicityInternal

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Category.{v₁} D]

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

section BeckComonadicity

/-- Dual to `Monad.CreatesColimitOfIsSplitPair`. -/
class CreatesLimitOfIsCosplitPair (F : C ⥤ D) where
  /-- If `f, g` is an `F`-cosplit pair, then `F` creates limits of `parallelPair f g`. -/
  out : ∀ {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], CreatesLimit (parallelPair f g) F

end BeckComonadicity
end
end Comonad
end CategoryTheory
end
