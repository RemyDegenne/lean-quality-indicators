public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section Lag

variable {K : Type} [Group K] [Finite K] {z : K}

omit [Finite K] in
theorem conj_comm_eq_inv (hz : z ∈ center K) {x₀ d : K} (hx : x₀ * x₀ ∈ zpowers z) :
    x₀⁻¹ * (x₀ * d * x₀⁻¹ * d⁻¹) * x₀ = (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ := by
  have hxi : x₀⁻¹ * x₀⁻¹ ∈ zpowers z := by
    have := inv_mem hx
    rwa [mul_inv_rev] at this
  have h1 : d * x₀⁻¹ * d⁻¹ = x₀⁻¹ * (x₀ * d * x₀⁻¹ * d⁻¹) := by group
  have h2 : (d * x₀⁻¹ * d⁻¹) * (d * x₀⁻¹ * d⁻¹) = x₀⁻¹ * x₀⁻¹ := by
    calc (d * x₀⁻¹ * d⁻¹) * (d * x₀⁻¹ * d⁻¹) = d * (x₀⁻¹ * x₀⁻¹) * d⁻¹ := by group
      _ = x₀⁻¹ * x₀⁻¹ := by
        rw [commute_of_mem_zpowers_of_mem_center hz hxi d, mul_inv_cancel_right]
  rw [h1] at h2
  calc x₀⁻¹ * (x₀ * d * x₀⁻¹ * d⁻¹) * x₀
      = (x₀⁻¹ * (x₀ * d * x₀⁻¹ * d⁻¹) * (x₀⁻¹ * (x₀ * d * x₀⁻¹ * d⁻¹))) *
          (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ * (x₀ * x₀) := by group
    _ = (x₀⁻¹ * x₀⁻¹) * (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ * (x₀ * x₀) := by rw [h2]
    _ = (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ * (x₀⁻¹ * x₀⁻¹) * (x₀ * x₀) := by
        rw [← commute_of_mem_zpowers_of_mem_center hz hxi]
    _ = (x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ := by group

end Lag
end CFSG.ComponentClassification.AS81
end
