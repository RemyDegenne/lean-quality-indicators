namespace P2MW.S_groupCohomology_mem_levelCoboundaries2_sUnitsMaxRep_of_zsmul_mem_of_val_mem

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option maxHeartbeats 3200000

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory groupCohomology ValuationSubring NumberField.LevelArith ExtCitation

noncomputable section

namespace P2MKumE

local notation "ℚb" => (AlgebraicClosure ℚ)

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

local instance isAlgebraicQbar_ke : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

local instance isAlgClosureQbar_ke : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

local instance normalQbar_ke : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

variable (p : ℕ) [hp : Fact p.Prime] (S : Finset Nat.Primes)

variable (D : Subgroup Γ)

section H90

variable {D}

variable (c : ↥D → Additive ℚbˣ) (hc1 : ∀ g h : ↥D, c (g * h) = c g + act D g (c h))
  (F₀ : IntermediateField ℚ ℚb) [FiniteDimensional ℚ F₀]
  (hcR : ∀ g s : ↥D, (s : Γ) ∈ F₀.fixingSubgroup → c (g * s) = c g)
  (L : IntermediateField ℚ ℚb) [FiniteDimensional ℚ L] [Normal ℚ L] (hL : F₀ ≤ L)
  (hcv : ∀ g : ↥D, ((Additive.toMul (c g) : ℚbˣ) : ℚb) ∈ L)

abbrev HD : Subgroup (L ≃ₐ[ℚ] L) := ((res L).comp D.subtype).range

end H90
end P2MKumE
end
end P2MW.S_groupCohomology_mem_levelCoboundaries2_sUnitsMaxRep_of_zsmul_mem_of_val_mem
