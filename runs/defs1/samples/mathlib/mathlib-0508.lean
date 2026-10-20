@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.Limits

section Pullback

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

variable {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g)

variable (f g) [PreservesLimit (cospan f g) G]

/-- If `G` preserves pullbacks and `C` has them, then the pullback cone constructed of the mapped
morphisms of the pullback cone is a limit. -/
def isLimitOfHasPullbackOfPreservesLimit [HasPullback f g] :
    have : G.map (pullback.fst f g) ≫ G.map f = G.map (pullback.snd f g) ≫ G.map g := by
      simp only [← G.map_comp, pullback.condition]
    IsLimit (PullbackCone.mk (G.map (pullback.fst f g)) (G.map (pullback.snd f g)) this) :=
  isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback f g)

end Pullback
end CategoryTheory.Limits
end
end
