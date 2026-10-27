public section

open ComplexConjugate ContinuousLinearMap InnerProductSpace

open scoped ComplexOrder

namespace Matrix.PosSemidef

open TauCeti

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]

variable {α : Type v}

variable {K : α → α → 𝕜}

/-- The canonical feature map into the Kolmogorov space.  It sends `a` to the reproducing-kernel
vector at `a`, evaluated on the scalar `1`. -/
noncomputable def kolmogorovFeature (hK : Matrix.PosSemidef K) (a : α) :
    KolmogorovSpace hK := by
  letI : Fact (positiveDefiniteKernelOperator K).PosSemidef :=
    ⟨posSemidef_positiveDefiniteKernelOperator hK⟩
  exact RKHS.kerFun (KolmogorovSpace hK) a 1

end Matrix.PosSemidef
end
