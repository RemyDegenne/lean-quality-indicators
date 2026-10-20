namespace P2MW.S_LanglandsTunnell_RankinSelberg_godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

open NumberField.AdelicLevel (diagOne)

open scoped Classical

set_option maxHeartbeats 1600000

namespace L1Box46

noncomputable section

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

attribute [local instance] AutomorphicForm.localGLBorel

attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)

local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

local notation "M2" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

local notation "νa" => (selfDualHaarAt ℚ p)

local notation "νx" => (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ)

section Factors

theorem integrable_f2 {Md : ℤ} (hMd : 1 ≤ Md) : Integrable (f2 p Md) νx := by
  unfold f2
  exact (integrable_indicator_iff (measurableSet_prinUnits p _)).2
    (integrableOn_const (prinUnits_lt_top p hMd).ne)

end Factors
end
end L1Box46
end P2MW.S_LanglandsTunnell_RankinSelberg_godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart
