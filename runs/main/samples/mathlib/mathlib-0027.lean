@[expose] public section

variable {𝕜 E : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E]

variable [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local notation "absR" => @abs ℝ _ _

namespace Submodule

variable (K : Submodule 𝕜 E)

noncomputable section

section orthogonalProjection

variable [K.HasOrthogonalProjection]

variable {K}

@[simp]
theorem orthogonalProjectionOnto_mem_subspace_eq_self (v : K) :
    K.orthogonalProjectionOnto v = v := by
  ext
  apply eq_starProjection_of_mem_of_inner_eq_zero <;> simp

end orthogonalProjection
end
end Submodule
end
