@[expose] public section

open CategoryTheory Opposite

universe u₁ v₁ u₂ v₂ w

namespace CategoryTheory.Subfunctor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {G : D ⥤ Type w}

variable {F : Dᵒᵖ ⥤ Type w} (S : Subfunctor F) (W : MorphismProperty D)

variable (J : C ⥤ D)

theorem isOneCoverDense_equivalence_iff [W.RespectsIso] (e : C ≌ D) :
    (S.precomp e.functor.op).IsOneCoverDense (W.inverseImage e.functor) ↔
      S.IsOneCoverDense W := by
  exact isOneCoverDense_precomp_iff S W e.functor

end CategoryTheory.Subfunctor
end
