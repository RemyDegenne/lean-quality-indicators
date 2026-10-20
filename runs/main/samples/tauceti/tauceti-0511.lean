public section

open CategoryTheory MulOpposite DirectSum

namespace TauCeti

universe uR uA uB uM uN uP

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

namespace DGRightModuleCat

@[simp]
theorem mem_extendScalars_obj_grading (f : DGAlgHom hA hB)
    (M : DGRightModuleCat.{uR, uA, max uB uM} hA) (q : ℤ)
    (x : (extendScalars f).obj M) :
    x ∈ ((extendScalars f).obj M).grading q ↔
      extendScalarsEquiv f M x ∈
        IsDGRightModule.extendScalarsGrading (M := M) (ℳ := M.grading) f q := by
  rw [IsDGRightModule.extendScalarsGrading_eq_tensorGrading]
  rfl

end DGRightModuleCat
end TauCeti
end
