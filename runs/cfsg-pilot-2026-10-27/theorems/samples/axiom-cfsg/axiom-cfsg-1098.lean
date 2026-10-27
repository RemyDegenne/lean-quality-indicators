public section

namespace CFSG.ASVolI

section F4dBaseRest

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

section Out

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

theorem burnsideF4d_mem_commutator_of_oTwoRes {G : Type} [Group G]
    (hO2 : oTwoRes (⊤ : Subgroup G) = ⊤) {x : G} (hx : x * x = 1) : x ∈ commutator G := by
  let T : Subgroup (Abelianization G) :=
    { carrier := {a | ∃ n : ℕ, Odd n ∧ a ^ n = 1}
      one_mem' := ⟨1, odd_one, one_pow 1⟩
      mul_mem' := by
        rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
        refine ⟨m * n, hm.mul hn, ?_⟩
        rw [mul_pow, pow_mul a m n, ha, one_pow, mul_comm m n, pow_mul b n m, hb, one_pow, one_mul]
      inv_mem' := by
        rintro a ⟨m, hm, ha⟩
        exact ⟨m, hm, by rw [inv_pow, ha, inv_one]⟩ }
  have hle : oTwoRes (⊤ : Subgroup G) ≤ T.comap (Abelianization.of : G →* Abelianization G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨-, m, hm, hy⟩
    exact ⟨m, hm, by rw [← map_pow, hy, map_one]⟩
  rw [hO2] at hle
  obtain ⟨n, hn, hxn⟩ := hle (Subgroup.mem_top x)
  have h2 : (Abelianization.of x) ^ 2 = 1 := by rw [pow_two, ← map_mul, hx, map_one]
  have hg : Nat.gcd 2 n = 1 := (Nat.coprime_two_left.mpr hn)
  have h1 : (Abelianization.of x) ^ (Nat.gcd 2 n) = 1 := pow_gcd_eq_one.mpr ⟨h2, hxn⟩
  rw [hg, pow_one] at h1
  rw [← Abelianization.ker_of (G := G), MonoidHom.mem_ker]
  exact h1

end Out
end F4dBaseRest
end CFSG.ASVolI
end
