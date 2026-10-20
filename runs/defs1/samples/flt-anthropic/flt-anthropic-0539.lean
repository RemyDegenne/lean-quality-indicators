namespace P2MW.S_LanglandsTunnell_CubicInduction_tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous

attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex

set_option autoImplicit false

open scoped TensorProduct

namespace WsC

namespace SplitAsm

open MvPolynomial

noncomputable section

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))

def gen₂ (q : P) (w : W) : P ⊗[ℂ] W :=
  ((D 0 1 (D 0 1 q)) ⊗ₜ[ℂ] w - ((D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w) + (D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w))) +
    ((D 0 2 (D 0 2 q)) ⊗ₜ[ℂ] w - ((D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w) + (D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w))) +
    ((D 1 2 (D 1 2 q)) ⊗ₜ[ℂ] w - ((D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w) + (D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w)))

end
end SplitAsm
end WsC
end P2MW.S_LanglandsTunnell_CubicInduction_tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous
