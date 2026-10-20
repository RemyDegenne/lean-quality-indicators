public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

attribute [instance] AcyclicResolution.hasHomology AcyclicResolution.quasiIso

namespace AcyclicResolution

variable {X A : C} (R : AcyclicResolution X A)

variable {B : C} (R' : AcyclicResolution X B)

variable {R'}

/-- One dimension shift along the canonical cycle short exact sequence. -/
@[expose] noncomputable def cyclesDimensionShift (n q : ℕ) (hq : 0 < q) :
    Ext X (R.cocomplex.cycles (n + 1)) q ≃+
      Ext X (R.cocomplex.cycles n) (q + 1) := by
  letI : Subsingleton (Ext X (R.cyclesShortComplex n).X₂ q) := by
    simpa [cyclesShortComplex] using R.extAcyclic n q hq
  letI : Subsingleton (Ext X (R.cyclesShortComplex n).X₂ (q + 1)) := by
    simpa [cyclesShortComplex] using R.extAcyclic n (q + 1) (by omega)
  exact covariantDimensionShift (R.cyclesShortComplex_shortExact n) X q

end AcyclicResolution
end CategoryTheory.Abelian.Ext
end
end
