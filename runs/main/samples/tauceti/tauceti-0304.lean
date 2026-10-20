public section

open Function Filter Topology

namespace ContinuousLinearMap

variable {𝕜 F V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

section Adjoint

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] [CompleteSpace V]

theorem starProjection_range_eq {B : F →L[𝕜] V} [B.range.HasOrthogonalProjection]
    (hB : IsUnit (adjoint B ∘L B)) :
    B.range.starProjection = B ∘L Ring.inverse (adjoint B ∘L B) ∘L adjoint B := by
  have hG : (adjoint B ∘L B) ∘L Ring.inverse (adjoint B ∘L B) = 1 :=
    Ring.mul_inverse_cancel _ hB
  ext v
  rw [comp_apply, comp_apply]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (LinearMap.mem_range_self (B : F →ₗ[𝕜] V) _) ?_
  rintro _ ⟨x, rfl⟩
  have h := congrArg (fun T : F →L[𝕜] F => T (adjoint B v)) hG
  simp only [comp_apply, one_apply_eq_self] at h
  rw [coe_coe, inner_sub_left]
  simp only [← adjoint_inner_left, h, sub_self]

end Adjoint
end ContinuousLinearMap
end
