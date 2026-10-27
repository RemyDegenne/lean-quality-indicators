public section

open scoped Matrix

namespace TauCeti

/-- The even reverse-unitary carrier of `Cl⁺(2,1)` is the real special linear group. -/
noncomputable def realCliffordTwoOneEvenUnitaryEquivSpecialLinear :
    CliffordAlgebra.evenUnitaryGroup (realCliffordForm 2 1) ≃*
      Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  CliffordAlgebra.evenUnitaryGroupEquivOfAlgEquiv (realCliffordForm 2 1)
    realCliffordTwoOneEvenEquivMatrix (fun A => A.det = 1)
    Matrix.SpecialLinearGroup.coeMonoidHom Matrix.SpecialLinearGroup.coeMonoidHom_injective
    (fun A hA => ⟨A, hA⟩) (fun _ _ => rfl) Matrix.SpecialLinearGroup.det_coe
    realCliffordTwoOne_reverseEven_mul_self_eq_one_iff_det_eq_one

end TauCeti
end
