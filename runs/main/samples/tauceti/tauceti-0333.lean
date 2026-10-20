public section

namespace TauCeti.Hodge.StandardWeightOne

open IsBaseChange

open Matrix

open scoped TensorProduct

variable (l : Type*)

noncomputable local instance moduleRatOfComplex : Module ℚ (ComplexSpace l) :=
  Module.restrictScalars ℚ ℂ (ComplexSpace l)

variable [Fintype l] [DecidableEq l]

theorem isPerfPair_riemannForm : (riemannForm l).IsPerfPair := by
  refine .of_bijective _ ?_
  have hJ : Function.Bijective fun x : Lattice l ↦ x ᵥ* J l ℤ :=
    Function.bijective_iff_has_inverse.mpr ⟨fun x ↦ -(x ᵥ* J l ℤ), fun x ↦ by
      simp only [vecMul_vecMul, J_squared, vecMul_neg, vecMul_one, neg_neg], fun x ↦ by
      simp only [neg_vecMul, vecMul_vecMul, J_squared, vecMul_neg, vecMul_one, neg_neg]⟩
  have h : ⇑(riemannForm l) = (Pi.basisFun ℤ (l ⊕ l)).toDualEquiv ∘ fun x ↦ x ᵥ* J l ℤ := by
    ext x : 1
    refine (Pi.basisFun ℤ (l ⊕ l)).ext fun i ↦ ?_
    rw [riemannForm_def, toBilin'_apply', Function.comp_apply, Module.Basis.toDualEquiv_apply,
      Module.Basis.toDual_apply_left, Pi.basisFun_repr, dotProduct_mulVec, Pi.basisFun_apply,
      dotProduct_single, mul_one]
  rw [h]
  exact (Pi.basisFun ℤ _).toDualEquiv.bijective.comp hJ

end TauCeti.Hodge.StandardWeightOne
end
