@[expose] public section

universe u₁ u₂ v₁ v₂ w t

namespace CategoryTheory

open Limits CategoryTheory.Functor

namespace PreGaloisCategory

attribute [instance] hasTerminal hasPullbacks hasFiniteCoproducts hasQuotientsByFiniteGroups

attribute [instance] preservesTerminalObjects preservesPullbacks preservesEpis
  preservesFiniteCoproducts reflectsIsos preservesQuotientsByFiniteGroups

variable {C : Type u₁} [Category.{u₂, u₁} C]
  (F : C ⥤ FintypeCat.{w})

variable [PreGaloisCategory C] [FiberFunctor F]

/-- The fiber of the pullback is the fiber product of the fibers. -/
noncomputable def fiberPullbackEquiv {X A B : C} (f : A ⟶ X) (g : B ⟶ X) :
    F.obj (pullback f g) ≃ { p : F.obj A × F.obj B // F.map f p.1 = F.map g p.2 } :=
  Iso.toEquiv (PreservesPullback.iso (F ⋙ FintypeCat.incl) f g ≪≫
    Types.pullbackIsoPullback (F.map f).hom (F.map g).hom)

end PreGaloisCategory
end CategoryTheory
end
