public section

namespace TauCeti

open Bornology Complex Filter MeasureTheory Metric Set Topology

open scoped ENNReal Real

variable {U : Set ℂ} {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}

theorem exists_tendsto_nhdsWithin_circleMap_image_Ioo (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (ζ : ℂ) {ρ : ℝ} {a b θ₀ : ℝ} (hab : a < b)
    (hab2π : b - a < 2 * π) (hθ₀ : θ₀ ∈ Icc a b)
    (hmemU : ∀ θ ∈ Ioo a b, circleMap ζ ρ θ ∈ U)
    (hfin : ∫⁻ θ in Ioo a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ ≠ ⊤) :
    ∃ v, Tendsto f (𝓝[circleMap ζ ρ '' Ioo a b] (circleMap ζ ρ θ₀)) (𝓝 v) :=
  exists_tendsto_of_clusterSetOn_subsingleton
    (isBounded_image_circleMap_image_Ioo_of_lintegral_ne_top hUo hf ζ hmemU
      hfin).isCompact_closure
    (fun _ hw => subset_closure (mem_image_of_mem f hw))
    (circleMap_mem_closure_image_Ioo ζ ρ hab hθ₀)
    (subsingleton_clusterSetOn_circleMap_image_Ioo hUo hf ζ hab hab2π hθ₀ hmemU hfin)

end TauCeti
end
