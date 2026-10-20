namespace P2MW.S_ModularCurve_exists_isParabolicHom_apply_eq_period

open scoped MatrixGroups

open UpperHalfPlane Filter Topology

namespace ModularCurve

namespace PeriodParabolic

p2m_open

open ModularCurve.Period

section Main

variable (N : ℕ) [NeZero N]

local notation "Γ" => CongruenceSubgroup.Gamma0 N

local notation "V" => CuspForm (CongruenceSubgroup.Gamma0 N) 2

theorem main :
    ∃ Φ : Additive Γ →+ Module.Dual ℂ V,
      IsParabolicHom Γ Φ ∧ ∀ γ : Γ, Φ (Additive.ofMul γ) = ModularCurve.period N γ :=
  ⟨periodHomDual N, isParabolicHom_periodHomDual N, periodHomDual_apply N⟩

end Main
end PeriodParabolic
end ModularCurve
end P2MW.S_ModularCurve_exists_isParabolicHom_apply_eq_period
