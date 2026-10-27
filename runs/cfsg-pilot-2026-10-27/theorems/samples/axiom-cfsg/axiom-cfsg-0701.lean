public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Holds

theorem le_conj_range_of_isElemAbelian_E6 {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpf : ¬ p ∣ f)
    {E : Subgroup (MulAut (adjointGroup .E6 K))} (hE : IsElemAbelian p E) :
    E ≤ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  obtain ⟨Θ, -, -, hker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hsq : ∀ y : Multiplicative (ZMod (exactE .E6)), y ^ 2 = 1 := by
    have h0 : ∀ z : ZMod 2, z + z = 0 := by decide
    intro y
    rw [pow_two]
    exact congrArg Multiplicative.ofAdd (h0 (Multiplicative.toAdd y))
  have hcard :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1
  intro e he
  have hep : e ^ p = 1 := hE.2 e he
  have h2 : (Θ e).2 = 1 := by
    refine TableBExc.eq_one_of_sq_of_pow_odd hodd (hsq _) ?_
    rw [← Prod.pow_snd, ← map_pow, hep, map_one, Prod.snd_one]
  have h1 : (Θ e).1 = 1 := by
    have hpσ : (Θ e).1 ^ p = 1 := by
      rw [← Prod.pow_fst, ← map_pow, hep, map_one, Prod.fst_one]
    have hdvd : orderOf (Θ e).1 ∣ f := by
      have := orderOf_dvd_natCard (Θ e).1
      rwa [hcard] at this
    have h3 : orderOf (Θ e).1 ∣ Nat.gcd p f := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpσ) hdvd
    rw [((Nat.Prime.coprime_iff_not_dvd hp).2 hpf).gcd_eq_one] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have hΘ1 : Θ e = 1 := Prod.ext h1 h2
  obtain ⟨g, a, hga⟩ := (hker _).1 hΘ1
  have hα : e = MulAut.conj g * exactNormalAut .E6 K a 1 0 :=
    eq_conj_mul_exactNormalAut_of_apply (σ := 1) (ε := 0) fun h => by
      rw [hga h, exactQ_zero, AutSt.units_map_entrywiseHom_one, inv_one, mul_one, mul_one]
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)) hp.one_lt
  rw [← TableBExc.pow_mul_eq_self_of_mod hk hep, pow_mul]
  exact Subgroup.pow_mem _ (TableBExc.pow_three_mem_inn_of_eq hα) k

end Holds
end CFSG.LocalAnalysis.GLTheoremA
end
