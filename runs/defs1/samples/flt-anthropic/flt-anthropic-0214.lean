namespace P2MW.S_LanglandsTunnell_RankinSelberg_godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

open NumberField.AdelicLevel (diagOne)

open scoped Classical

namespace L2Box46

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

local notation "ψp" => (NumberField.StandardAddChar.psiLocal ℚ p)

section Box

def Φb (L Mb Mc Md : ℤ) : M2 → ℂ := fun X => Set.indicator (boxSet p L Mb Mc Md) (fun _ => (1 : ℂ)) X

end Box
end
end L2Box46
end P2MW.S_LanglandsTunnell_RankinSelberg_godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart
