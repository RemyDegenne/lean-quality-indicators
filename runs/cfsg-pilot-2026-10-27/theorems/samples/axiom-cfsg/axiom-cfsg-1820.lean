public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {ι ρ : K ≃+* K}

variable (C : UCtx ι ρ) (M : Matrix (Fin 3) (Fin 3) K)

include C

theorem rows_onLine (hall : AllNorm ι ρ M) (B : IsoBasis ι ρ) (hM : ∀ z, ∃ y, M *ᵥ y = z)
    {a : Fin 3 → K} (ha : Ratv ρ a) (haI : herm ι a a = 0) (ha0 : a ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ OnLine ρ c (rowv ι M a) := by
  have hrow : ∀ j, rowv ι M a j = ∑ k, (B.span j).choose k * Bf ι M a (B.g k) := by
    intro j
    rw [Bf_rowv_single]
    conv_lhs => rw [(B.span j).choose_spec.2]
    exact Bf_sum_right M a _ _
  have hex : ∃ k, Bf ι M a (B.g k) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply ha0
    refine (rowv_eq_zero_iff (ι := ι) M hM a).mp ?_
    funext j
    rw [hrow j]
    simp [hcon]
  obtain ⟨k₀, hk₀⟩ := hex
  set d₀ := Bf ι M a (B.g k₀) with hd₀
  have hrat : ∀ k, ρ (Bf ι M a (B.g k) / d₀) = Bf ι M a (B.g k) / d₀ := by
    intro k
    by_cases hk : k = k₀
    · subst hk; rw [← hd₀, div_self hk₀, map_one]
    · set sc := herm ι (B.g k₀) (B.g k) with hsc
      have hsc0 : sc ≠ 0 := B.nonorth k₀ k (Ne.symm hk)
      have hρs : ρ sc = sc := UCtx.ρ_herm C (B.rat k₀) (B.rat k)
      have hf : Ratv ρ (sc⁻¹ • B.g k) := ratv_smul (by rw [map_inv₀, hρs]) (B.rat k)
      have hfI : herm ι (sc⁻¹ • B.g k) (sc⁻¹ • B.g k) = 0 := by
        rw [herm_smul_left, herm_smul_right, B.iso k, mul_zero, mul_zero]
      have hef : herm ι (B.g k₀) (sc⁻¹ • B.g k) = 1 := by
        rw [herm_smul_right, ← hsc, inv_mul_cancel₀ hsc0]
      have := layer1 C M hall ha (B.rat k₀) hf haI (B.iso k₀) hfI hef hk₀
      rw [Bf_smul_right, ← hd₀] at this
      have e : sc⁻¹ * Bf ι M a (B.g k) / d₀ = sc⁻¹ * (Bf ι M a (B.g k) / d₀) := by ring
      rw [e, map_mul, map_inv₀, hρs] at this
      have hsinv : sc⁻¹ ≠ 0 := inv_ne_zero hsc0
      exact mul_left_cancel₀ hsinv this
  refine ⟨d₀, hk₀, fun j => ∑ k, (B.span j).choose k * (Bf ι M a (B.g k) / d₀), ?_, ?_⟩
  · intro j
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, (B.span j).choose_spec.1 k, hrat k]
  · funext j
    rw [hrow j]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
end
