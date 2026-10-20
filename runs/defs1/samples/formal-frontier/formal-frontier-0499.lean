public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

attribute [instance] AcyclicResolution.hasHomology AcyclicResolution.quasiIso

section SameUniverse

variable {D : Type u} [Category.{v} D] [Abelian D] [HasExt.{v} D]

namespace AcyclicResolution

variable {X A : D} (R : AcyclicResolution X A)

/-- The additive coyoneda functor applied termwise to an acyclic resolution. -/
noncomputable abbrev homComplex : CochainComplex AddCommGrpCat.{v} ℕ :=
  ((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj R.cocomplex

end AcyclicResolution
end SameUniverse
end CategoryTheory.Abelian.Ext
end
end
