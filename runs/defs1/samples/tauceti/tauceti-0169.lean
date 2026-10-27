public section

open PowerSeries

namespace TauCeti.completedGroupAlgebra

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
  (e : Γ ≃ₜ* Multiplicative (ZMod 2) × Multiplicative ℤ_[2])

section Level

variable (m : ℕ)

/-- **The levels of `Γ ≅ C₂ × ℤ₂`.** The open normal subgroup `U_m = e⁻¹({1} × 2^m ℤ₂)` of `Γ`:
the elements whose `C₂`-coordinate is `1` and whose `ℤ₂`-coordinate is divisible by `2 ^ m`
(`mem_dyadicLevel_iff`). The levels are cofinal among the open normal subgroups of `Γ`
(`exists_dyadicLevel_le`), and through the dyadic coordinate the kernel of the projection of
`ℤ₂[[Γ]]` to `U_m` is the principal ideal `((1 + X) ^ (2 ^ m) - 1)`
(`ker_proj_comp_dyadicCoordinate`). -/
noncomputable def dyadicLevel : OpenNormalSubgroup Γ :=
  ((openNormalSubgroupBot (Multiplicative (ZMod 2))).prod (padicIntLevel 2 m)).comap e
    (map_continuous e)

end Level
end TauCeti.completedGroupAlgebra
end
