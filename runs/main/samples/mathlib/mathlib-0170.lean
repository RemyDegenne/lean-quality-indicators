@[expose] public section

variable {𝕜 E : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E]

variable [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local notation "absR" => @abs ℝ _ _

namespace Submodule

variable (K : Submodule 𝕜 E)

noncomputable section

variable {K}

theorem norm_sq_eq_add_norm_sq_starProjection (x : E) (S : Submodule 𝕜 E)
    [S.HasOrthogonalProjection] :
    ‖x‖ ^ 2 = ‖S.starProjection x‖ ^ 2 + ‖Sᗮ.starProjection x‖ ^ 2 :=
  norm_sq_eq_add_norm_sq_projection x S

end
end Submodule
end
