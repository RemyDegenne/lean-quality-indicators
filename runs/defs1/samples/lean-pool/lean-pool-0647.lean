@[expose] public section

open TauCeti.DavisKahan.Angle

open TauCeti.DavisKahan.Sylvester

namespace TauCeti

namespace DavisKahan1970

open scoped InnerProductSpace BigOperators

open TauCeti.DavisKahanExt

open TauCeti.DavisKahan

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

/-- **The complexification of a real unbounded-compression bundle.**

The compression is complexified coordinatewise as a closed operator and then read through
the canonical adapter `complexifySubmoduleEquiv` between `RealComplexification ↥Z` and
`↥(complexifySubmodule Z)`; the residual, being bounded, is complexified and read through
the same adapter.  No ambient operator enters. -/
def complexifyUnboundedCompressionTrialData
    (D : UnboundedCompressionTrialData Z) :
    UnboundedCompressionTrialData (complexifySubmodule Z) where
  compression :=
    TauCeti.DavisKahan.unitaryConjugate (complexifySubmoduleEquiv Z)
      (ExactSinTheta.PartialMapComplexification.complexify D.compression)
      (ExactSinTheta.PartialMapComplexification.isSelfAdjoint_complexify
        D.compression_isSelfAdjoint)
  compression_isSelfAdjoint :=
    TauCeti.DavisKahan.unitaryConjugate_isSelfAdjoint _ _ _
  residual :=
    complexify D.residual ∘L
      (complexifySubmoduleEquiv Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  residual_orthogonal := by
    intro w w'
    have hperp : ∀ z : Z, D.residual z ∈ Zᗮ := by
      intro z
      rw [Submodule.mem_orthogonal]
      intro y hy
      rw [real_inner_comm]
      exact D.residual_orthogonal z ⟨y, hy⟩
    set e := complexifySubmoduleEquiv Z with he
    set u := e.symm w with hu
    have hmem : complexify D.residual u ∈ complexifySubmodule Zᗮ := by
      rw [mem_complexifySubmodule]
      exact ⟨hperp _, hperp _⟩
    rw [complexifySubmodule_orthogonal] at hmem
    exact Submodule.inner_left_of_mem_orthogonal w'.2 hmem

end
end DavisKahan1970
end TauCeti
end
