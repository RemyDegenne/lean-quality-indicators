public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries IsLocalRing Filter

open scoped NormedField Valued

variable {σ K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

local notation "T" => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

local notation "T°" => Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))

local notation "Tint" => IsRestricted.subring (R := 𝒪[K]) (fun _ : σ ↦ 1)

section Reduction

@[simp]
theorem restrictedReduction_X (i : σ) (h : (⟨X i, isRestricted_X _ i⟩ : T) ∈ T°) :
    restrictedReduction ⟨⟨X i, isRestricted_X _ i⟩, h⟩ = MvPolynomial.X i := by
  classical
  have : (⟨⟨X i, isRestricted_X _ i⟩, h⟩ : T°) =
      restrictedIntegerEquiv
        ⟨((MvPolynomial.X i : MvPolynomial σ 𝒪[K]) : MvPowerSeries σ 𝒪[K]),
          MvPolynomial.isRestricted _ _⟩ :=
    Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun t ↦ by
      rw [coeff_restrictedIntegerEquiv]
      simp only [MvPolynomial.coe_X, coeff_X]
      split_ifs <;> simp
  rw [this, restrictedReduction_restrictedIntegerEquiv, MvPolynomial.map_X]

end Reduction
end TauCeti.MvPowerSeries
end
