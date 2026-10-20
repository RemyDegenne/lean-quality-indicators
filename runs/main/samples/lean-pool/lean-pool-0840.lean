@[expose] public section

namespace TauCeti

namespace DavisKahan

namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal

noncomputable section

universe u vE vF vG vH vE1 vF1 vE2 vF2

theorem hilbertSchmidtNorm_operatorModulus
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) :
    (ContinuousLinearMap.modulus A).hilbertSchmidtNorm = A.hilbertSchmidtNorm :=
  SameApproximationSingularSequence.hilbertSchmidtNorm_eq
    (modulus_hasSameApproximationNumbers A)

end
end ExactSinTheta
end DavisKahan
end TauCeti
end
