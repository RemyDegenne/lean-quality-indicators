namespace P2MW.S_AutomorphicForm_twistedCentralizer_detShell_eq_of_gram_conjAe_of_neg

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace ProperUnifCore

open Matrix Topology Filter Set

def ι : GL (Fin 2) ℝ →* GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map Complex.ofRealHom

end ProperUnifCore
end
end P2MW.S_AutomorphicForm_twistedCentralizer_detShell_eq_of_gram_conjAe_of_neg
