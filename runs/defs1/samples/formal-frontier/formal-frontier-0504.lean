set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace LinearEquiv

universe u

/-- Choose finite right-linear coordinates on a free kernel of a right-unimodular
coefficient row. Finite generation follows from the specified splitting. -/
noncomputable def rightCoefficientFreeKernelCoordinates (R : Type u) [Ring R]
    {n : ℕ} (a : Fin n → R) (ha : Bass.IsRightUnimodular a)
    (hfree : Module.Free Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a))) :
    Σ m : ℕ, LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R) := by
  classical
  letI : Module.Free Rᵐᵒᵖ
      (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a)) := hfree
  letI : Module.Finite Rᵐᵒᵖ
      (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a)) :=
    LinearMap.finite_rightCoefficientKernel R a ha
  letI : Module.Free Rᵐᵒᵖ R :=
    Module.Free.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ (M := R)).symm
  let ι := Module.Free.ChooseBasisIndex Rᵐᵒᵖ
    (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a))
  letI : Fintype ι := Module.Free.ChooseBasisIndex.fintype Rᵐᵒᵖ
    (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a))
  let m := Fintype.card ι
  exact ⟨m,
    ((Module.Free.chooseBasis Rᵐᵒᵖ _).repr).trans
      ((Finsupp.linearEquivFunOnFinite Rᵐᵒᵖ Rᵐᵒᵖ ι).trans
        ((LinearEquiv.piCongrRight
          (fun _ : ι ↦ (MulOpposite.opLinearEquiv Rᵐᵒᵖ (M := R)).symm)).trans
          (LinearEquiv.piCongrLeft Rᵐᵒᵖ (fun _ : Fin m ↦ R)
            (Fintype.equivFin ι))))⟩

end LinearEquiv
end
