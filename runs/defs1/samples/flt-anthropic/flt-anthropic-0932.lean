namespace P2MW.S_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier Topology

open scoped ENNReal NNReal

noncomputable section

namespace Ws23Arch

scoped instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology

def iwB (q : ℝ × ℝ × ℝ) : GL (Fin 2) ℝ :=
  if h : 0 < q.2.1 ∧ 0 < q.2.2 then
    upperUnit (q.2.2 * q.2.1) (q.2.2 * q.1) q.2.2 (mul_pos h.2 h.1).ne' h.2.ne'
  else 1

end Ws23Arch
end
end P2MW.S_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa
