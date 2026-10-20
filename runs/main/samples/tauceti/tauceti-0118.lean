public section

namespace TauCeti

open CategoryTheory Limits ContCohomology

variable (p : ℕ) [Fact p.Prime] (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
  [Module.Finite ℚ_[p] L] [ValuativeExtension ℚ_[p] L]

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]

theorem exists_zmultiples_eq_top_groupCohomology_two_res_padicCompletionUnits
    (S : Subgroup (L ≃ₐ[K] L)) :
    ∃ u : groupCohomology
        (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 2,
      AddSubgroup.zmultiples u = ⊤ ∧
        Nat.card (groupCohomology
          (Rep.res S.subtype (Rep.of (padicCompletionUnitsRepresentation p L K))) 2) =
          p ^ padicValNat p (Nat.card S) :=
  (groupCohomology_res_padicCompletionUnits p K L S).2

end TauCeti
end
