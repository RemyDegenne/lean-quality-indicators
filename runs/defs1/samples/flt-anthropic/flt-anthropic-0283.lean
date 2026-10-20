namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_smoothingOperator_eq_archConvN_and_exists_levelSet_subset

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm Matrix MeasureTheory Topology Filter TopologicalSpace

namespace LanglandsTunnell

namespace CubicInduction

namespace ArchConvCalculus

p2m_open

def liftE (e : E33) (he : (Matrix.of e).det ≠ 0) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  toGinf (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)

end ArchConvCalculus
end CubicInduction
end LanglandsTunnell
end
end P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_smoothingOperator_eq_archConvN_and_exists_levelSet_subset
