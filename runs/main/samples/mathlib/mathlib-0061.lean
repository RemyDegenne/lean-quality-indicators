@[expose] public section

noncomputable section

open RCLike Real Filter Topology Finsupp

open scoped ComplexConjugate

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section BasicProperties_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local postfix:90 "†" => starRingEnd _

export InnerProductSpace (norm_sq_eq_re_inner)

variable (𝕜)

variable (F)

variable {F}

variable {𝕜}

theorem inner_re_zero_right (x : E) : re ⟪x, 0⟫ = 0 := by
  simp only [inner_zero_right, map_zero]

end BasicProperties_Seminormed
end
end
