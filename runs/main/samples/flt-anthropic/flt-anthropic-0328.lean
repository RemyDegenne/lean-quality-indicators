namespace P2MW.S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex

set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups ModularForm

namespace RelrankNormSol

open ModularForm UpperHalfPlane SlashInvariantForm Polynomial IntermediateField

section Norm

variable (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)} [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ}

noncomputable scoped instance : Fintype (Cos Γ Γ') := Fintype.ofFinite _

variable (f g : ModularForm (GG Γ') k)

variable (hT' : ModularGroup.T ∈ Γ') (hle : Γ' ≤ Γ)

include hT' hle

theorem sum_qExpansion_coeffForm_mul_pow_eq_zero :
    ∑ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
      qExpansion 1 (coeffForm Γ f g i : ℍ → ℂ) * qExpansion 1 (f : ℍ → ℂ) ^ i *
        qExpansion 1 (g : ℍ → ℂ) ^ (Nat.card (Cos Γ Γ') - i) = 0 := by
  set R : ℍ → ℂ := ∑ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
    (coeffForm Γ f g i : ℍ → ℂ) * (f : ℍ → ℂ) ^ i * (g : ℍ → ℂ) ^ (Nat.card (Cos Γ Γ') - i) with hR
  have hR0 : R = 0 := by
    funext τ
    simp only [hR, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    exact sum_coeffForm_mul_pow_eq_zero Γ f g τ
  have hnice : ∀ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
      Nice ((coeffForm Γ f g i : ℍ → ℂ) * (f : ℍ → ℂ) ^ i * (g : ℍ → ℂ) ^ (Nat.card (Cos Γ Γ') - i)) :=
    fun i _ => ((nice_of_HH Γ hT' hle _).mul ((nice_of_GG Γ hT' hle f).pow i)).mul
      ((nice_of_GG Γ hT' hle g).pow _)
  have h := congrArg (qExpansion 1) hR0
  rw [qExpansion_zero, hR, qExpansion_sum' _ hnice] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [qExpansion_mul ((nice_of_HH Γ hT' hle _).mul ((nice_of_GG Γ hT' hle f).pow i))
      ((nice_of_GG Γ hT' hle g).pow _),
    qExpansion_mul (nice_of_HH Γ hT' hle _) ((nice_of_GG Γ hT' hle f).pow i),
    qExpansion_pow' (nice_of_GG Γ hT' hle f), qExpansion_pow' (nice_of_GG Γ hT' hle g)]

end Norm
end RelrankNormSol
end
end P2MW.S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex
