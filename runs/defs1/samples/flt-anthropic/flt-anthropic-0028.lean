namespace P2MW.S_ModularCurve_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

set_option linter.unusedSectionVars false

open scoped TensorProduct ModularForm MatrixGroups

noncomputable section

namespace ModularCurve

namespace LinAuxW

p2m_open

section Main

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
  (K : Type*) [Field K] [Algebra (ZMod p) K]

local notation "Γ" => CohCarrier.GammaH M H

local notation "A" => (⊥ : Subring ℂ)

local notation "L" => CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)

local notation "Ω₀" => CuspForm.IntTwoCuspForms M H p

local notation "F̄" => qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))

variable (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ)

def expZ (y : L) : PowerSeries ℤ := (exists_isIntegralQExp p M hpM H hHp W e (y : CuspForm Γ 2) y.2).choose

end Main
end LinAuxW
end ModularCurve
end
end P2MW.S_ModularCurve_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH
