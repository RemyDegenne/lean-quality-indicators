public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

open scoped Pointwise

section AbstractKq

variable {P Q H : Type} [CommGroup P] [CommGroup Q] [Group H] [Finite P] [Finite Q] [Finite H]

theorem d3q_kq_range_le (μ : P →* Q) (hμ : Function.Surjective μ) (Θ₀ : H →* MulAut P)
    (Θ : H →* MulAut Q) (hint : ∀ (h : H) (p : P), μ (Θ₀ h p) = Θ h (μ p))
    (hker : Θ.ker ≤ Θ₀.ker) (k : ℕ) : kq Θ.range k ≤ kq Θ₀.range k := by
  by_cases htop : kq Θ₀.range k = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
  rw [← hr]
  obtain ⟨A, hA, hAk, hAr⟩ := kq_le_iff.mp (le_of_eq hr.symm)
  have hker' : Θ₀.ker ≤ Θ.ker := by
    intro h hh
    rw [MonoidHom.mem_ker] at hh ⊢
    refine MulEquiv.ext fun q => ?_
    obtain ⟨p, rfl⟩ := hμ q
    rw [← hint, hh]
    rfl
  have hker_eq : Θ.ker = Θ₀.ker := le_antisymm hker hker'
  have hΘeq : ∀ x y : H, Θ₀ x = Θ₀ y → Θ x = Θ y := by
    intro x y hxy
    have h1 : x⁻¹ * y ∈ Θ₀.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 := hker' h1
    rw [MonoidHom.mem_ker, map_mul, map_inv] at h2
    exact inv_mul_eq_one.mp h2
  set Ã : Subgroup H := A.comap Θ₀ with hÃ
  set B : Subgroup (MulAut Q) := Ã.map Θ with hB
  have hAÃ : Ã.map Θ₀ = A := by
    rw [hÃ, Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hA.1
  have hBne : B ≠ ⊥ := by
    intro hB0
    apply hA.2.1
    rw [← hAÃ]
    rw [hB, Subgroup.map_eq_bot_iff] at hB0
    exact (Subgroup.map_eq_bot_iff _).mpr (hB0.trans hker)
  have hBel : IsElemAbelian2 B := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      apply hΘeq
      rw [map_mul, map_mul]
      exact hA.2.2.1 _ (Subgroup.mem_comap.mp hx) _ (Subgroup.mem_comap.mp hy)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, ← map_one Θ]
      apply hΘeq
      rw [map_pow, map_one]
      exact hA.2.2.2 _ (Subgroup.mem_comap.mp hx)
  have hcomm : ∀ n : ℕ, commIter ⊤ B n ≤ (commIter ⊤ A n).map μ := by
    intro n
    induction n with
    | zero =>
      show (⊤ : Subgroup Q) ≤ (⊤ : Subgroup P).map μ
      rw [Subgroup.map_top_of_surjective μ hμ]
    | succ n ih =>
      show commSub (commIter ⊤ B n) B ≤ (commSub (commIter ⊤ A n) A).map μ
      refine (commSub_mono ih le_rfl).trans ?_
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨Θ₀ x p * p⁻¹, Subgroup.subset_closure
        ⟨Θ₀ x, Subgroup.mem_comap.mp hx, p, hp, rfl⟩, ?_⟩
      rw [map_mul, map_inv, hint]
  have hBk : commSeries B k = ⊥ := by
    have h1 := hcomm k
    rw [show commIter ⊤ A k = commSeries A k from rfl, hAk, Subgroup.map_bot] at h1
    exact le_bot_iff.mp h1
  have hcard : Nat.card B = Nat.card A := by
    have h1 := B1More.card_map_mul_card_inf_ker Ã Θ
    have h2 := B1More.card_map_mul_card_inf_ker Ã Θ₀
    rw [hAÃ] at h2
    rw [hker_eq] at h1
    have hpos : 0 < Nat.card ↥(Ã ⊓ Θ₀.ker) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  have hfix : (fixV A).map μ ≤ fixV B := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨x, hx, rfl⟩
    rw [← hint]
    exact congrArg μ (hv _ (Subgroup.mem_comap.mp hx))
  have hidx : rkIdx (fixV B) ≤ rkIdx (fixV A) := by
    refine le_trans (b := rkIdx ((fixV A).map μ)) ?_ ?_
    · exact padicValNat_two_le_of_dvd Subgroup.index_ne_zero_of_finite
        (Subgroup.index_dvd_of_le hfix)
    · exact padicValNat_two_le_of_dvd Subgroup.index_ne_zero_of_finite
        (Subgroup.index_map_dvd _ hμ)
  refine kq_le_iff.mpr ⟨B, ⟨Subgroup.map_le_range _ _, hBne, hBel⟩, hBk, ?_⟩
  refine le_trans ?_ hAr
  unfold rAV
  have hrk : rk ↥B = rk ↥A := by
    unfold rk
    rw [hcard]
  rw [hrk]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hidx) (Nat.cast_nonneg _)

end AbstractKq
end CFSG.Quasithin
end
