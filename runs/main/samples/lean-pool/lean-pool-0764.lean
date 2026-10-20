@[expose] public section

noncomputable section

open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem

open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

omit [IsTotallyComplex K] in
open Classical in
theorem integrableOn_centeredClassThetaPoissonCorrection
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (centeredClassThetaPoissonCorrection K s)
      (positiveUnitFundamentalParamSet (K := K)) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hreflect : (1 - s).re < 0 := by simp_all
  apply IntegrableOn.congr_fun
    ((integrableOn_positive_logarithmicMellinWeight K hreflect).sub
      (integrableOn_positive_logarithmicMellinWeight_neg K hs0))
    _ measurableSet_positiveUnitFundamentalParamSet
  intro y _
  exact centeredClassThetaPoissonCorrection_eq K s y |>.symm

end NumberField.Odlyzko
end
end
