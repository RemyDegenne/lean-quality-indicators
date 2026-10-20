@[expose] public section

open NormedField Set Filter

open scoped NNReal Pointwise Topology Uniformity

variable {R R' 𝕜 𝕜₂ 𝕜₃ 𝕝 E E₂ E₃ F ι : Type*}

export SeminormClass (map_smul_eq_mul)

namespace Seminorm

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {p q : Seminorm 𝕜 E} {x : E}

section Classical

protected theorem coe_iSup_eq {ι : Sort*} {p : ι → Seminorm 𝕜 E} (hp : BddAbove (range p)) :
    ↑(⨆ i, p i) = ⨆ i, ((p i : Seminorm 𝕜 E) : E → ℝ) := by
  rw [← sSup_range, Seminorm.coe_sSup_eq hp]
  exact iSup_range' (fun p : Seminorm 𝕜 E => (p : E → ℝ)) p

end Classical
end NormedField
end Seminorm
end
