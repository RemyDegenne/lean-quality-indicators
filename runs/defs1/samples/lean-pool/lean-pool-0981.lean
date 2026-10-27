@[expose] public section

namespace TauCeti

open scoped ENNReal

universe u v w

section Symmetric

variable {𝕜 : Type u} [RCLike 𝕜]

variable {E F : Type v}

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **The compact operators as a symmetric ideal family.**

Adjoint-invariance of the carrier is Schauder's theorem
(`ContinuousLinearMap.isCompactOperator_adjoint_iff`); adjoint-invariance of the
gauge is then the isometry of the adjoint, exactly as for the operator-norm
family. -/
noncomputable def compactOperatorFamily (𝕜 : Type u) [RCLike 𝕜] :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  toOperatorIdealFamily := compactOperatorIdealFamily 𝕜
  gauge_adjoint A := by
    classical
    by_cases hA : IsCompactOperator A
    · have hAdj : IsCompactOperator (ContinuousLinearMap.adjoint A) :=
        ContinuousLinearMap.isCompactOperator_adjoint hA
      rw [gauge_compactOperatorIdealFamily, gauge_compactOperatorIdealFamily,
        ite_eq_left hAdj, ite_eq_left hA, ← ofReal_norm, ← ofReal_norm,
        ContinuousLinearMap.adjoint.norm_map]
    · have hAdj : ¬ IsCompactOperator (ContinuousLinearMap.adjoint A) := fun h =>
        hA (ContinuousLinearMap.isCompactOperator_adjoint_iff.mp h)
      rw [gauge_compactOperatorIdealFamily, gauge_compactOperatorIdealFamily,
        ite_eq_right hAdj, ite_eq_right hA]

end Symmetric
end TauCeti
end
