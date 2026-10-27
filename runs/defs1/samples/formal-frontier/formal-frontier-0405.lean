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

/-- The dimension-shift cokernel is canonically the degree-one Ext group of
the cycles in the same degree. -/
@[expose] noncomputable def cyclesCokernelIso (n : ℕ)
    [Subsingleton (Ext X (R.cyclesShortComplex n).X₂ 1)] :
    cokernel ((extFunctorObj X 0).map
      (R.cocomplex.toCycles n (n + 1))) ≅
        ↧(Ext X (R.cocomplex.cycles n) 1) :=
  covariantCokernelIso (R.cyclesShortComplex_shortExact n) X

end AcyclicResolution
end SameUniverse
end CategoryTheory.Abelian.Ext
end
end
