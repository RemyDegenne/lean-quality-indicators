public section

open CategoryTheory

namespace TauCeti.DGRightModuleCat

universe uR uB uM

variable {R : Type uR} {B : Type uB}
  [CommRing R] [Ring B] [Algebra R B]
  {Bₙ : ℤ → Submodule R B} [GradedAlgebra Bₙ]
  {dB : B →ₗ[R] B} {hB : IsDGAlgebra Bₙ dB}

@[simp]
theorem toScalarBimodule_grading (M : DGRightModuleCat.{uR, uB, uM} hB) :
    M.toScalarBimodule.grading = M.grading := (rfl)

end TauCeti.DGRightModuleCat
end
