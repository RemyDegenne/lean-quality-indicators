public section

noncomputable section

open Set

open scoped ENNReal BigOperators

namespace TauCeti

universe u v

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] {μ : PMF ι} {ν : PMF κ}
  {c : ι × κ → ℝ} {φ : ι → ℝ} {ψ : κ → ℝ} {f : ι × κ → ℝ}

theorem TransportMatrix.forall_cost_le_and_forall_finiteDualValue_le_iff (A : TransportMatrix μ ν)
    (hfeas : ∀ i j, φ i + ψ j ≤ c (i, j)) :
    ((∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c) ∧
        ∀ φ' ψ', (∀ i j, φ' i + ψ' j ≤ c (i, j)) →
          finiteDualValue μ ν φ' ψ' ≤ finiteDualValue μ ν φ ψ)
      ↔ ∀ i j, A i j ≠ 0 → φ i + ψ j = c (i, j) := by
  rw [← A.cost_eq_finiteDualValue_iff hfeas]
  constructor
  · rintro ⟨hmin, hmax⟩
    obtain ⟨B, φ', ψ', -, hfeas', heq⟩ := exists_cost_eq_finiteDualValue c μ ν
    have h1 := hmin B
    have h2 := hmax φ' ψ' hfeas'
    have h3 := A.finiteDualValue_le_cost hfeas
    linarith
  · intro heq
    refine ⟨fun B ↦ ?_, fun φ' ψ' hfeas' ↦ ?_⟩
    · rw [heq]
      exact B.finiteDualValue_le_cost hfeas
    · rw [← heq]
      exact A.finiteDualValue_le_cost hfeas'

end TauCeti
end
end
