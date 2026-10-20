@[expose] public section

universe uι uκ uD

namespace KTheory

variable {ι : Type uι} (D : ι → Type uD) (κ : ι → Type uκ)

variable [∀ i, DivisionRing (D i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [∀ i, Nonempty (κ i)] [Finite ι]

namespace K0

section Basis

theorem matrixFamilyBasis_eq_ofClass (i : ι) :
    matrixFamilyBasis D κ i =
      ofClass (∀ j, Matrix (κ j) (κ j) (D j))
        (ProjectiveClass.matrixFamilyRowClass D κ i) := by
  classical
  apply (matrixFamilyEquiv D κ).injective
  funext j
  rw [matrixFamilyEquiv_ofClass, ProjectiveClass.matrixFamilyEquiv_matrixFamilyRowClass]
  have h := congrFun (matrixFamilyEquiv_basis D κ i) j
  simpa [Pi.single_apply] using h

end Basis
end K0
end KTheory
end
