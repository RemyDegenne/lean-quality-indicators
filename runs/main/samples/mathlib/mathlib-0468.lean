noncomputable section

open Module RCLike

open scoped ComplexConjugate

variable {𝕜 E F G : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open InnerProductSpace

@[expose] public section

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

section linearIsometryEquiv

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

namespace ContinuousLinearMap

theorem inner_map_map_iff_adjoint_comp_self (u : H →L[𝕜] K) :
    (∀ x y : H, ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜) ↔ adjoint u ∘L u = 1 := by
  refine ⟨fun h ↦ ext fun x ↦ ?_, fun h ↦ ?_⟩
  · refine ext_inner_right 𝕜 fun y ↦ ?_
    simpa [star_eq_adjoint, adjoint_inner_left] using h x y
  · simp [← adjoint_inner_left, ← comp_apply, h]

end ContinuousLinearMap
end linearIsometryEquiv
end Unitary
end
end
