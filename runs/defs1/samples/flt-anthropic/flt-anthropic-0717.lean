namespace P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open MeasureTheory Filter NumberField NumberField.AdelicBox IsDedekindDomain

open scoped TensorProduct TensorProduct.RightActions Topology Classical

noncomputable section

namespace Ws25L3

p2m_reactivate

section Split

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {ι : Type} [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (v : Fin 2 → L)

attribute [local instance] Mu1.algAL

def Xif (y : ι → FiniteAdeleRing (𝓞 K) K) : Fin 2 → FiniteAdeleRing (𝓞 L) L :=
  fun j => (Mu1.Xi K L b v (finAdele K y) j).2

end Split
end Ws25L3
end
end P2MW.S_AutomorphicForm_exists_twistedCentralizer_coe_eq_sum_map_tmul_and_tensorPlace_eq_one_of_forall_exists
