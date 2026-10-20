@[expose] public section

open TauCeti.DavisKahan.Angle

open TauCeti.DavisKahan.Sylvester

open TauCeti.DavisKahan.TanTheta

namespace TauCeti

namespace DavisKahan1970

open scoped InnerProductSpace BigOperators

open TauCeti.DavisKahanExt

open TauCeti.DavisKahan

open TauCeti.DavisKahan.ExactSinTheta

open TauCeti.DavisKahan.ExactSinTheta.ComplexificationApproximation

open TauCeti.DavisKahan.TanTheta

open TauCeti.DavisKahan.TanTheta

open TauCeti.RealComplexification

open TauCeti.DavisKahan.Foundation.RealComplexification

open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

variable {Z V : Submodule ℝ E} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]

theorem approximationSingularValue_complexifyTrialData_residual
    (data : Theorem63TrialData Z V) (n : ℕ) :
    approximationSingularValue n (complexifyTrialData data).residual =
      approximationSingularValue n data.residual := by
  let U := LinearIsometryEquiv.refl ℂ (RealComplexification E)
  let W := complexifySubmoduleEquiv Z
  have hcoord :
      U.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          complexify data.residual ∘L
          W.symm.toContinuousLinearEquiv.toContinuousLinearMap =
        (complexifyTrialData data).residual := by
    apply ContinuousLinearMap.ext
    intro z
    rfl
  have hsame := SameApproximationSingularValues.of_isometricEquiv_comp U W hcoord
  exact (hsame n).symm.trans (approximationSingularValue_complexify data.residual n)

end
end DavisKahan1970
end TauCeti
end
