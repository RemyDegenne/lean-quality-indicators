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

/-- The induced canonical isomorphism on homology. -/
@[expose] noncomputable def extZeroHomologyIsoHomology (n : ℕ) :
    R.extZeroComplex.homology n ≅ R.homComplex.homology n :=
  HomologicalComplex.homologyMapIso R.extZeroComplexIsoHomComplex n

end AcyclicResolution
end SameUniverse
end CategoryTheory.Abelian.Ext
end
end
