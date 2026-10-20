@[expose] public section

noncomputable section

open RCLike Real Module Finsupp

open scoped ComplexConjugate

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section OrthonormalSets_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {ι : Type*} (𝕜)

variable {𝕜}

theorem Orthonormal.inner_finsupp_eq_sum_left {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι →₀ 𝕜) :
    ⟪linearCombination 𝕜 v l₁, linearCombination 𝕜 v l₂⟫ = l₁.sum fun i y => conj y * l₂ i := by
  simp [l₁.linearCombination_apply, Finsupp.sum_inner, hv.inner_right_finsupp, inner_smul_left]

end OrthonormalSets_Seminormed
end
end
