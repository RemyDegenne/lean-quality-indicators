namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt

attribute [-instance] CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction

set_option autoImplicit false

open scoped Quaternion

open QuaternionAlgebra

open Codiff29 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (c : ℍ[ℚ, a, b]) :
    (∀ x ∈ Λ, ∃ n : ℤ, (n : ℚ) = trd (c * x)) ↔ (μ : ℍ[ℚ, a, b]) * c ∈ Λ := by
  have hO : IsOrder Λ := hΛ.1
  have hqp : q.Prime := Fact.out
  have hq'p : q'.Prime := Fact.out
  set s : ℚ := ((q * q' : ℕ) : ℚ) with hs
  have hs0 : s ≠ 0 := by rw [hs]; exact_mod_cast Nat.mul_ne_zero hqp.ne_zero hq'p.ne_zero
  have hspos : 0 < s := by rw [hs]; exact_mod_cast Nat.mul_pos hqp.pos hq'p.pos
  have hμμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = (-s) • (1 : ℍ[ℚ, a, b]) := by rw [hμ, neg_smul]
  have hnrdμ : nrd (μ : ℍ[ℚ, a, b]) = s := by
    have := nrd_eq_neg_of_mul_self (by linarith) hμμ; rw [this, neg_neg]
  have hμμy : ∀ y : ℍ[ℚ, a, b], (μ : ℍ[ℚ, a, b]) * ((μ : ℍ[ℚ, a, b]) * y) = (-s) • y := fun y => by
    rw [← mul_assoc, hμμ, smul_mul_assoc, one_mul]

  have hcop : IsCoprime (q : ℤ) (q' : ℤ) :=
    Nat.Coprime.isCoprime ((Nat.coprime_primes hqp hq'p).mpr (Ne.symm hqq'))
  constructor
  ·
    intro hc
    obtain ⟨N, hN0, hNc⟩ := exists_natCast_smul_mem_of_mem_span (Λ := Λ) (y := c)
      (by rw [hO.spanTop]; trivial)
    have hy : (((q * q' : ℕ) : ℤ) • c) ∈ Λ := descent hqq' hB Λ hΛ c hc N hN0 hNc
    set y : ℍ[ℚ, a, b] := ((q * q' : ℕ) : ℤ) • c with hydef

    have htr : ∀ (r : ℕ), (r = q ∨ r = q') → ∀ z ∈ Λ, ∃ t : ℤ, trd (y * z) = (r : ℚ) * t := by
      intro r hr z hz
      obtain ⟨n, hn⟩ := trd_nsmul_mul Λ c hc (q * q') z hz
      rcases hr with rfl | rfl
      · exact ⟨(q' : ℤ) * n, by rw [hydef, hn]; push_cast; ring⟩
      · exact ⟨(q : ℤ) * n, by rw [hydef, hn]; push_cast; ring⟩
    have hnq := hΛ.dvd_nrd_of_forall_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt hB Λ q (Or.inl rfl) y hy (htr q (Or.inl rfl))
    have hnq' := hΛ.dvd_nrd_of_forall_dvd_trd_mul_of_isIndefiniteRamifiedExactlyAt hB Λ q' (Or.inr rfl) y hy (htr q' (Or.inr rfl))

    have hμq : ∃ n : ℤ, nrd (μ : ℍ[ℚ, a, b]) = (q : ℚ) * n := ⟨q', by rw [hnrdμ, hs]; push_cast; ring⟩
    have hμq' : ∃ n : ℤ, nrd (μ : ℍ[ℚ, a, b]) = (q' : ℚ) * n := ⟨q, by rw [hnrdμ, hs]; push_cast; ring⟩
    obtain ⟨w₁, hw₁, h₁⟩ := hΛ.exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt hB Λ q
      (Or.inl rfl) _ μ.2 _ hy hμq hnq
    obtain ⟨w₂, hw₂, h₂⟩ := hΛ.exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt hB Λ q'
      (Or.inr rfl) _ μ.2 _ hy hμq' hnq'
    obtain ⟨u, v, huv⟩ := hcop

    have hμy : (μ : ℍ[ℚ, a, b]) * y = ((q * q' : ℕ) : ℤ) • (v • w₁ + u • w₂) := by
      have e1 : ((q * q' : ℕ) : ℤ) • (v • w₁ + u • w₂) =
          ((q' : ℤ) * v) • ((q : ℤ) • w₁) + ((q : ℤ) * u) • ((q' : ℤ) • w₂) := by
        push_cast
        module
      rw [e1, ← h₁, ← h₂, ← add_smul, show (q' : ℤ) * v + (q : ℤ) * u = 1 by linarith [huv], one_smul]
    have hmem : v • w₁ + u • w₂ ∈ Λ := Λ.add_mem (Λ.smul_mem _ hw₁) (Λ.smul_mem _ hw₂)

    have : ((q * q' : ℕ) : ℤ) • ((μ : ℍ[ℚ, a, b]) * c) = ((q * q' : ℕ) : ℤ) • (v • w₁ + u • w₂) := by
      rw [← hμy, hydef, mul_smul_comm]
    rw [zsmul_right_cancel (by exact_mod_cast Nat.mul_ne_zero hqp.ne_zero hq'p.ne_zero) this]
    exact hmem
  ·
    intro hm x hx
    set m : ℍ[ℚ, a, b] := (μ : ℍ[ℚ, a, b]) * c with hmdef
    have hcx : c * x = (-s⁻¹) • ((μ : ℍ[ℚ, a, b]) * (m * x)) := by
      rw [hmdef, mul_assoc, hμμy, smul_smul]
      rw [show (-s⁻¹ * -s) = 1 by field_simp, one_smul]
    have hmx : m * x ∈ Λ := hO.mul_mem hm hx
    have hw : (μ : ℍ[ℚ, a, b]) * (m * x) ∈ Λ := hO.mul_mem μ.2 hmx
    obtain ⟨k, hk⟩ := (hO.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hmx).1
    have hnw : nrd ((μ : ℍ[ℚ, a, b]) * (m * x)) = s * k := by rw [nrd_mul', hnrdμ, hk]
    obtain ⟨t₁, ht₁⟩ := hΛ.dvd_trd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt hB Λ q (Or.inl rfl) _ hw
      ⟨q' * k, by rw [hnw, hs]; push_cast; ring⟩
    obtain ⟨t₂, ht₂⟩ := hΛ.dvd_trd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt hB Λ q' (Or.inr rfl) _ hw
      ⟨q * k, by rw [hnw, hs]; push_cast; ring⟩

    have hqt : (q : ℤ) * t₁ = (q' : ℤ) * t₂ := by
      have : ((q : ℤ) * t₁ : ℚ) = ((q' : ℤ) * t₂ : ℚ) := by push_cast; rw [← ht₁, ← ht₂]
      exact_mod_cast this
    have hdvd : (q' : ℤ) ∣ t₁ := by
      have h' : (q' : ℤ) ∣ (q : ℤ) * t₁ := ⟨t₂, hqt⟩
      exact (IsCoprime.symm hcop).dvd_of_dvd_mul_left h'
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨-t, ?_⟩
    rw [hcx, trd_smul', ht₁, ht, hs]
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqp.ne_zero
    have hq0' : (q' : ℚ) ≠ 0 := by exact_mod_cast hq'p.ne_zero
    push_cast
    field_simp

end P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt
