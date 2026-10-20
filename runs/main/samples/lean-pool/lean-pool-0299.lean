@[expose] public section

section rankOneLm

variable {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open scoped BigOperators

open scoped BigOperators

theorem rankOne.smul_right_to_left {𝕜 E₁ E₂ : Type _} [RCLike 𝕜] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂]
    (x : E₁) (y : E₂) (r : 𝕜) :
    rankOne 𝕜 x (r • y) = rankOne 𝕜 (star r • x) y := by
  simp_all

end rankOneLm
end
