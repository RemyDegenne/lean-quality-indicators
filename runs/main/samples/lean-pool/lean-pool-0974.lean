@[expose] public section

namespace PerUnitMerge

lemma complement_map_injective
    (n d : ℕ) (hd_dvd : d ∣ n) (b : ℕ) (hb_pos : 1 ≤ b) (hb_lt : b < d) :
    ∀ v₁ v₂ : ℕ,
      v₁ < n → v₁ % d = b → n < 2 * v₁ →
      v₂ < n → v₂ % d = b → n < 2 * v₂ →
      (n - v₁ - (d - b)) / d = (n - v₂ - (d - b)) / d →
      v₁ = v₂ := by
  intro v₁ v₂ hv₁_lt hv₁_mod hv₁_big hv₂_lt hv₂_mod hv₂_big hdiv_eq
  have hd_pos : 0 < d := by omega
  have h_dvd₁ := complement_div_d_dvd n d hd_dvd b hb_pos hb_lt v₁ hv₁_lt hv₁_mod hv₁_big
  have h_dvd₂ := complement_div_d_dvd n d hd_dvd b hb_pos hb_lt v₂ hv₂_lt hv₂_mod hv₂_big
  have h_le₁ := d_sub_b_le_n_sub_v n d hd_dvd b hb_pos hb_lt v₁ hv₁_lt hv₁_mod hv₁_big
  have h_le₂ := d_sub_b_le_n_sub_v n d hd_dvd b hb_pos hb_lt v₂ hv₂_lt hv₂_mod hv₂_big
  have h_eq := eq_of_dvd_div_eq _ _ d hd_pos h_dvd₁ h_dvd₂ hdiv_eq
  omega

end PerUnitMerge
end
