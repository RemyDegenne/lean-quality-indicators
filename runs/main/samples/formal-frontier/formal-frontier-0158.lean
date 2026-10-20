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

lemma cyclesDimensionShift_naturality
    {B : C} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex)
    (n q : ℕ) (hq : 0 < q) (x : Ext X (R.cocomplex.cycles (n + 1)) q) :
    R'.cyclesDimensionShift n q hq
        (x.comp (mk₀ (HomologicalComplex.cyclesMap f (n + 1))) (add_zero q)) =
      (R.cyclesDimensionShift n q hq x).comp
        (mk₀ (HomologicalComplex.cyclesMap f n)) (add_zero (q + 1)) := by
  dsimp [cyclesDimensionShift, covariantDimensionShift]
  exact covariantDimensionShift_naturality
    (R.cyclesShortComplex_shortExact n) (R'.cyclesShortComplex_shortExact n)
      (R.cyclesShortComplexMap f n) X q x

end AcyclicResolution
end CategoryTheory.Abelian.Ext
end
end
