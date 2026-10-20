@[expose] public section

noncomputable section

open RCLike Real Filter Topology Finsupp

open scoped ComplexConjugate

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Norm_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local notation "IK" => @RCLike.I 𝕜 _

theorem norm_add_sq (x y : E) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 := by
  repeat' rw [sq (M := ℝ), ← @inner_self_eq_norm_mul_norm 𝕜]
  rw [inner_add_add_self, two_mul]
  simp only [add_assoc, add_left_inj, add_right_inj, map_add]
  rw [← inner_conj_symm, conj_re]

end Norm_Seminormed
end
end
