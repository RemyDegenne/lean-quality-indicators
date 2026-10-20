namespace P2MW.S_AutomorphicForm_isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 160000

noncomputable section

namespace Ws23

namespace CuspAvg

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal IsDedekindDomain

open AutomorphicForm AutomorphicForm.WindowedSiegel

open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

variable {K : Type} [Field K] [NumberField K]

section Riemann

variable (K)

variable {K}

def partE (m : ℕ) : Fin (partN (K := K) m) → Set (Kc K) :=
  (exists_partition (K := K) (1 / ((m : ℝ) + 1)) (by positivity)).choose_spec.choose

end Riemann
end CuspAvg
end Ws23
end
end P2MW.S_AutomorphicForm_isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn
