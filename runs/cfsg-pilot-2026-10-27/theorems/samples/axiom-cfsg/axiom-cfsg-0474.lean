public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.GH74.Uniqueness.Bender

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open scoped Pointwise

theorem uc22s13xf_le_borel_of_odd {K : Type} [Group K] [Finite K]
    {n i e : ℕ} (hK : BenderType K n i e) (Q : Sylow 2 K) {A : Subgroup K}
    (hA : Odd (Nat.card A)) (hAQ : (A : Set K) * Q = Q * A) : A ≤ borel (Q : Subgroup K) := by
  classical
  haveI := hK.isSimple
  obtain ⟨t₀, h₀⟩ := hK.exists_benderCore Q
  by_cases hX : A ⊔ (Q : Subgroup K) = ⊤
  swap
  · exact le_sup_left.trans (h₀.le_borel_of_le le_sup_right hX)
  exfalso
  set P : Subgroup K := (Q : Subgroup K)
  have hAP : (A : Set K) * (P : Set K) = (P : Set K) * A := hAQ
  have hset : ((A ⊔ P : Subgroup K) : Set K) = (A : Set K) * P :=
    CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hAP
  have hfac : ∀ g : K, ∃ a ∈ A, ∃ u ∈ P, a * u = g := by
    intro g
    have hg : g ∈ ((A ⊔ P : Subgroup K) : Set K) := by
      rw [hX]
      exact Subgroup.mem_top g
    rw [hset] at hg
    exact Set.mem_mul.mp hg
  have hA₀ : Odd (Nat.card ↥(A ⊓ borel P)) := hA.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨t, ht, htM, hA₀D⟩ := uc22s13xf_exists_cartan_of_le_borel hK Q inf_le_right hA₀
  have h := h₀.of_involution ht htM
  have hti : t⁻¹ = t := inv_eq_of_mul_self ht
  have hDA : ∀ d ∈ cartan P t, d ∈ A := by
    intro d hd
    obtain ⟨a, ha, u, hu, rfl⟩ := hfac d
    have haM : a ∈ borel P := by
      have h1 := (borel P).mul_mem (cartan_le_borel P t hd) ((borel P).inv_mem (le_borel P hu))
      rwa [mul_inv_cancel_right] at h1
    have haD : a ∈ cartan P t := hA₀D (Subgroup.mem_inf.mpr ⟨ha, haM⟩)
    have huD : u ∈ cartan P t := by
      have h1 := (cartan P t).mul_mem ((cartan P t).inv_mem haD) hd
      rwa [inv_mul_cancel_left] at h1
    have hu1 : u ∈ P ⊓ cartan P t := Subgroup.mem_inf.mpr ⟨hu, huD⟩
    rw [h.inf_eq, Subgroup.mem_bot] at hu1
    rw [hu1, mul_one]
    exact ha
  obtain ⟨a, ha, u, hu, hau⟩ := hfac t
  have haD : ∀ d ∈ cartan P t, a⁻¹ * d * a ∈ cartan P t := by
    intro d hd
    refine hA₀D (Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem (A.inv_mem ha) (hDA d hd)) ha, ?_⟩)
    have h1 : a⁻¹ * d * a = u * (t⁻¹ * d * t) * u⁻¹ := by
      rw [← hau]
      group
    rw [h1, hti]
    exact (borel P).mul_mem ((borel P).mul_mem (le_borel P hu)
      (cartan_le_borel P t (h.cartan_mul_mul hd))) ((borel P).inv_mem (le_borel P hu))
  have hcomm : ∀ d ∈ cartan P t, u * d = d * u := by
    intro d hd
    have h1 : u * d * u⁻¹ ∈ cartan P t := by
      have h2 : u * d * u⁻¹ = a⁻¹ * (t * d * t⁻¹) * a := by
        rw [← hau]
        group
      rw [h2, hti]
      exact haD _ (h.cartan_mul_mul hd)
    have h2 : u * d * u⁻¹ * d⁻¹ ∈ P := by
      have hdP : d * u⁻¹ * d⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (cartan_le_borel P t hd) u⁻¹).mp (P.inv_mem hu)
      have h3 := P.mul_mem hu hdP
      rwa [show u * (d * u⁻¹ * d⁻¹) = u * d * u⁻¹ * d⁻¹ by group] at h3
    have h3 : u * d * u⁻¹ * d⁻¹ ∈ P ⊓ cartan P t :=
      Subgroup.mem_inf.mpr ⟨h2, (cartan P t).mul_mem h1 ((cartan P t).inv_mem hd)⟩
    rw [h.inf_eq, Subgroup.mem_bot] at h3
    calc u * d = u * d * u⁻¹ * d⁻¹ * (d * u) := by group
      _ = d * u := by rw [h3, one_mul]
  have hn2 : 2 ≤ n := hK.two_le.2
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hDcard : Nat.card (cartan P t) = (2 ^ n - 1) * e := h.card_cartan
  have hDpos : 0 < Nat.card (cartan P t) := Nat.card_pos
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with he0 | he0
    · rw [he0, mul_zero] at hDcard
      omega
    · exact he0
  have h3e : 3 * e ≤ Nat.card (cartan P t) := by
    rw [hDcard]
    exact Nat.mul_le_mul_right e (by omega)
  obtain ⟨d, hd, hd1⟩ : ∃ d ∈ cartan P t, d ≠ 1 := by
    rcases (cartan P t).bot_or_exists_ne_one with hbot | hex
    · rw [hbot, Subgroup.card_bot] at h3e
      omega
    · exact hex
  have hu1 : u = 1 := by
    rcases hK.cases' with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨rfl, -, -⟩
    · exact h.eq_one_of_commute_cartan Q.isPGroup' hd hd1 hu (hcomm d hd)
    · exact h.eq_one_of_commute_cartan Q.isPGroup' hd hd1 hu (hcomm d hd)
    · by_contra hu1
      have hdu : d * u * d⁻¹ * u⁻¹ ∈ rootCenter P := by
        rw [← hcomm d hd, mul_inv_cancel_right, mul_inv_cancel]
        exact (rootCenter P).one_mem
      have hz := hK.fixedPointFree_unitary Q ht htM hd hd1 hu hdu
      have hcard := h.card_cartan_inf_centralizer hz hu1
      have hle : cartan P t ≤ centralizer ({u} : Set K) := fun x hx =>
        Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff.mp hy]
          exact hcomm x hx
      rw [inf_eq_left.mpr hle] at hcard
      omega
  have htA : t ∈ A := by
    rw [← hau, hu1, mul_one]
    exact ha
  have ht1 : t ≠ 1 := fun h1 => htM (by rw [h1]; exact (borel P).one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht) ht1
  have hdvd := Subgroup.orderOf_dvd_natCard A htA
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hA) (even_iff_two_dvd.mpr hdvd)

end CFSG.LocalAnalysis.UniquenessCase.UC22
end
