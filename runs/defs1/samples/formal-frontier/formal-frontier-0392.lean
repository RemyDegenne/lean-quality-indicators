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

/-- A map of resolutions induces a map on the degree-zero Ext complexes. -/
noncomputable abbrev extZeroComplexMap {B : D} (R' : AcyclicResolution X B)
    (f : R.cocomplex ⟶ R'.cocomplex) : R.extZeroComplex ⟶ R'.extZeroComplex :=
  ((extFunctorObj X 0).mapHomologicalComplex (ComplexShape.up ℕ)).map f

end AcyclicResolution
end SameUniverse
end CategoryTheory.Abelian.Ext
end
end
