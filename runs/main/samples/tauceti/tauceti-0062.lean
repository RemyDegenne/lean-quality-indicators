public section

noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]

theorem commute_starProjection_diagBlock (A : E →L[𝕜] E) :
    Commute U.starProjection (U.diagBlock A) := by
  simp only [diagBlock, starProjection_orthogonal', ← ContinuousLinearMap.mul_def]
  have hP := U.isIdempotentElem_starProjection
  have h0 := hP.mul_one_sub_self
  have h1 := hP.one_sub_mul_self
  set P := U.starProjection
  -- Both products reduce to `P A P`, since `P (1 - P) = (1 - P) P = 0`.
  have hPP (B : E →L[𝕜] E) : P * (P * B) = P * B := by rw [← mul_assoc, hP.eq]
  have h0' (B : E →L[𝕜] E) : P * ((1 - P) * B) = 0 := by rw [← mul_assoc, h0, zero_mul]
  rw [commute_iff_eq]
  simp only [mul_add, add_mul, mul_assoc, hP.eq, h1, hPP, h0', mul_zero, add_zero]

end Submodule
end
end
