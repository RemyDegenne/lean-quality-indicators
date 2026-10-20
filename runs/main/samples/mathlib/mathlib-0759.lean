public section

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local notation "absR" => @abs ℝ _ _

open Finsupp Submodule RCLike Real InnerProductSpace

open LinearMap (ker range)

variable (K : Submodule 𝕜 E)

open Module Submodule

section OrthonormalBasis

variable {v : Set E}

open Module Submodule Set

variable [FiniteDimensional 𝕜 E]

theorem maximal_orthonormal_iff_basis_of_finiteDimensional (hv : Orthonormal 𝕜 ((↑) : v → E)) :
    (∀ u ⊇ v, Orthonormal 𝕜 ((↑) : u → E) → u = v) ↔ ∃ b : Basis v 𝕜 E, ⇑b = ((↑) : v → E) := by
  rw [maximal_orthonormal_iff_orthogonalComplement_eq_bot hv]
  rw [Submodule.orthogonal_eq_bot_iff]
  have hv_coe : range ((↑) : v → E) = v := by simp
  constructor
  · refine fun h => ⟨Basis.mk hv.linearIndependent _, Basis.coe_mk _ ?_⟩
    convert h.ge
  · rintro ⟨h, coe_h⟩
    rw [← h.span_eq, coe_h, hv_coe]

end OrthonormalBasis
end
