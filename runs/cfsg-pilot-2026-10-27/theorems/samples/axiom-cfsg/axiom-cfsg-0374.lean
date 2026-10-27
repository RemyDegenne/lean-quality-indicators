public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.C13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod

open CFSG.LieType.BorelTits

open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_one_of_conj_odd {Γ : Type*} [Group Γ] {g u c : Γ} {m k : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) (hck : c ^ 2 ^ k = 1) (hgc : g * c = c * g) (h : g * u * g⁻¹ = c * u) :
    c = 1 := by
  have hpow : ∀ j : ℕ, g ^ j * u * (g ^ j)⁻¹ = c ^ j * u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcj : g * c ^ j * g⁻¹ = c ^ j := by
        rw [(Commute.pow_right hgc j).eq]; group
      calc g ^ (j + 1) * u * (g ^ (j + 1))⁻¹ = g * (g ^ j * u * (g ^ j)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = (g * c ^ j * g⁻¹) * (g * u * g⁻¹) := by rw [ih]; group
        _ = c ^ (j + 1) * u := by rw [hcj, h, pow_succ, mul_assoc]
  have h1 : c ^ m = 1 := by
    have h2 := hpow m
    rw [hgm, inv_one, one_mul, mul_one] at h2
    calc c ^ m = c ^ m * u * u⁻¹ := by group
      _ = 1 := by rw [← h2, mul_inv_cancel]
  have h2 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
  have hodd : Odd (orderOf c) := Odd.of_dvd_nat hm h2
  have : orderOf c = 1 :=
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)).eq_one_of_dvd h3
  exact orderOf_eq_one_iff.mp this

end CFSG.Quasithin.F53.Stellmacher.S43.Even.C13
end
