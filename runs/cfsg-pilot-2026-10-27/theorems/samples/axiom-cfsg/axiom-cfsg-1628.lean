public section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

namespace CFSG.Quasithin.S15223P4.D1

section Cards

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M]

theorem card_eq_card_map_mul_card_ker (ρ : Γ →* M) (hρ : Function.Surjective ρ) {Q : Subgroup Γ}
    (hkQ : ρ.ker ≤ Q) : Nat.card Q = Nat.card (Q.map ρ) * Nat.card ρ.ker := by
  have : Finite M := Finite.of_surjective ρ hρ
  have h1 : Nat.card ρ.ker * Nat.card M = Nat.card Γ := by
    have := Subgroup.card_ker_mul_card_range ρ
    rwa [MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top] at this
  have hQ : (Q.map ρ).comap ρ = Q := Subgroup.comap_map_eq_self hkQ
  have hidx : Q.index = (Q.map ρ).index := by
    conv_lhs => rw [← hQ]
    exact Subgroup.index_comap_of_surjective (H := Q.map ρ) hρ
  have a := Subgroup.card_mul_index Q
  have b := Subgroup.card_mul_index (Q.map ρ)
  have hpos : 0 < Q.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [hidx] at a hpos
  have : Nat.card Q * (Q.map ρ).index = Nat.card (Q.map ρ) * Nat.card ρ.ker * (Q.map ρ).index := by
    rw [a, ← h1, ← b]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

end Cards
end CFSG.Quasithin.S15223P4.D1
end
