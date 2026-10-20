namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq

set_option autoImplicit false

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel TopCat

open scoped MatrixGroups Pointwise

universe u v

namespace WGenH

section Generic

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

variable (Mdl : CurveModel K L) (ψ : Mdl.C ⟶ Mdl.C) [IsIso ψ]

theorem inseparable_genericPoint : Inseparable (genericPoint Mdl.C) (ψ.base (genericPoint Mdl.C)) := by
  rw [base_genericPoint]

end Generic
end WGenH
end P2MW.S_ModularCurve_XHDRModelAtP_exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq
