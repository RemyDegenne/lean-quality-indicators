public section

open CategoryTheory MulOpposite

namespace TauCeti

universe u

variable {R : Type u} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

namespace DGRightModuleCat

variable (M N P : DGRightModuleCat.{u, u, u} h)

/-- Homogeneous morphisms of the differential graded category, identified with right-module
cochains through the equality of their Hom complexes. -/
noncomputable def dgHomLinearEquivCochains (n : ℤ) :
    DGHom R n M N ≃ₗ[R]
      dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) n :=
  (eqToIso (congrArg (fun K : CochainComplex (ModuleCat R) ℤ => K.X n)
    (dgHomComplex_eq M N))).toLinearEquiv

end DGRightModuleCat
end TauCeti
end
