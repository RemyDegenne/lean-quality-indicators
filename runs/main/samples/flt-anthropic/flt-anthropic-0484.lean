namespace P2MW.S_Ihara_pow_card_mem_mennickeQ_mul

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Inl_A3_CompositeStep

namespace Ihara

p2m_open

open Subgroup Matrix

open scoped MatrixGroups

open scoped commutatorElement

universe u

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Torsion

variable (q : ℕ)

variable [NeZero q]

theorem pow_card_mem_mennickeQ_mul_impl (m' m₅ m₆ : ℕ) [NeZero m'] [NeZero m₅] [NeZero m₆]
    (hcop : Nat.Coprime m' (m₅ * m₆)) (h56 : Nat.Coprime m₅ m₆) (hm'q : Nat.Coprime m' q)
    (hm''q : Nat.Coprime (m₅ * m₆) q) (hmq : Nat.Coprime (m' * (m₅ * m₆)) q) (hm'n : Nat.Coprime m' (q ^ 2 - 1))
    (hsat : (q ^ 2 - 1) ∣ m₅ * m₆) (h5 : ∀ p : ℕ, p.Prime → p ∣ m₅ → 5 ≤ p)
    (hP1 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → _root_.commutator (SL(2, ZMod (p ^ n))) = ⊤)
    (hP2 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → HasTrivialSchurMultiplier (SL(2, ZMod (p ^ n))))
    (hN' : MennickeCSP m' q hm'q) (hsurj' : Function.Surjective (slAwayReduction m' q hm'q))
    (hZ'' : mennickeZ q (m₅ * m₆) hm''q = ⊤)
    (hhabel'' : principalCongruenceAway (m₅ * m₆) q hm''q ≤
      _root_.commutator (SL(2, ZAway q)) ⊔ mennickeQ q (m₅ * m₆))
    (hsurj'' : Function.Surjective (slAwayReduction (m₅ * m₆) q hm''q))
    {x : SL(2, ZAway q)} (hx : x ∈ principalCongruenceAway (m' * (m₅ * m₆)) q hmq) :
    x ^ Nat.card (SL(2, ZMod m₆)) ∈ mennickeQ q (m' * (m₅ * m₆)) := by
  haveI : NeZero (m₅ * m₆) := ⟨Nat.mul_ne_zero (NeZero.ne m₅) (NeZero.ne m₆)⟩

  have hstem' : HasTrivialSchurMultiplier (SL(2, ZMod m')) :=
    (commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod hP1 hP2 m'
      (fun p hp hpm => five_le_of_prime_dvd_block q m' hp hpm hm'q hm'n)).2
  rw [mennickeQ_mul_eq_inf q m' (m₅ * m₆) hcop hm'q hm''q hmq hm'n hsat hN' hsurj' hstem', Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  ·
    have hx' : x ∈ principalCongruenceAway m' q hm'q := mem_principalCongruenceAway_left_of_mul q hcop hm'q hm''q hmq hx
    have hN'eq : principalCongruenceAway m' q hm'q = mennickeQ q m' := hN'
    rw [hN'eq] at hx'
    exact Subgroup.pow_mem _ hx' _
  ·
    have hx'' : x ∈ principalCongruenceAway (m₅ * m₆) q hm''q :=
      mem_principalCongruenceAway_right_of_mul q hcop hm'q hm''q hmq hx
    have hQ''N : mennickeQ q (m₅ * m₆) ≤ (slAwayReduction (m₅ * m₆) q hm''q).ker :=
      normalClosure_le_principalCongruenceAway _ q hm''q
    let π₀ : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆) →* SL(2, ZMod (m₅ * m₆)) :=
      QuotientGroup.lift (mennickeQ q (m₅ * m₆)) (slAwayReduction (m₅ * m₆) q hm''q) hQ''N
    let π : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆) →* SL(2, ZMod m₅) × SL(2, ZMod m₆) :=
      (slZModMulEquiv h56).toMonoidHom.comp π₀
    have hπ_mk : ∀ g : SL(2, ZAway q), π (QuotientGroup.mk g) = slZModMulEquiv h56 (slAwayReduction (m₅ * m₆) q hm''q g) :=
      fun g => rfl
    have hπker : ∀ g : SL(2, ZAway q),
        (QuotientGroup.mk g : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) ∈ π.ker ↔
          g ∈ principalCongruenceAway (m₅ * m₆) q hm''q := by
      intro g
      rw [MonoidHom.mem_ker, hπ_mk, MulEquiv.map_eq_one_iff, mem_principalCongruenceAway_iff]
    have hπsurj : Function.Surjective π := by
      intro Y
      obtain ⟨g, hg⟩ := hsurj'' ((slZModMulEquiv h56).symm Y)
      exact ⟨QuotientGroup.mk g, by rw [hπ_mk, hg, MulEquiv.apply_symm_apply]⟩
    have hcent : π.ker ≤ Subgroup.center _ := by
      intro k hk
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
      have hgN := (hπker g).mp hk
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hco : (h * g)⁻¹ * (g * h) = ⁅h⁻¹, g⁻¹⁆⁻¹ := by
        simp only [commutatorElement_def, _root_.mul_inv_rev, inv_inv]
        group
      rw [hco]
      refine Subgroup.inv_mem _ ?_
      have hhZ : h⁻¹ ∈ mennickeZ q (m₅ * m₆) hm''q := hZ'' ▸ Subgroup.mem_top _
      exact (mem_mennickeZ_iff q (m₅ * m₆) hm''q h⁻¹).mp hhZ g⁻¹ (Subgroup.inv_mem _ hgN)
    have hxker : (QuotientGroup.mk x : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) ∈ π.ker := (hπker x).mpr hx''
    have hxc : (QuotientGroup.mk x : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) ∈
        _root_.commutator (SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) := by
      have hx_mem : x ∈ ((_root_.commutator (SL(2, ZAway q)) ⊔ mennickeQ q (m₅ * m₆) :
          Subgroup SL(2, ZAway q)) : Set SL(2, ZAway q)) := hhabel'' hx''
      rw [Subgroup.mul_normal] at hx_mem
      obtain ⟨c, hc, w, hw, hcw⟩ := Set.mem_mul.mp hx_mem
      have hmkw : (QuotientGroup.mk w : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) = 1 :=
        (QuotientGroup.eq_one_iff w).mpr hw
      have hmkx : (QuotientGroup.mk x : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) = QuotientGroup.mk c := by
        rw [← hcw, QuotientGroup.mk_mul, hmkw, mul_one]
      rw [hmkx]
      have hmaple : Subgroup.map (QuotientGroup.mk' (mennickeQ q (m₅ * m₆))) (_root_.commutator (SL(2, ZAway q))) ≤
          _root_.commutator (SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) := by
        rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
        exact Subgroup.commutator_mono le_top le_top
      exact hmaple (Subgroup.mem_map_of_mem _ hc)

    obtain ⟨hperf₅, hstem₅⟩ := commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod hP1 hP2 m₅ h5
    have hF₆ : ∀ (E' : Type) [Group E'] (π' : E' →* SL(2, ZMod m₆)), Function.Surjective π' →
        π'.ker ≤ Subgroup.center E' → ∀ y ∈ π'.ker, y ∈ _root_.commutator E' →
          y ^ Nat.card (SL(2, ZMod m₆)) = 1 := by
      intro E' _ π' hs hc y hy hyc
      have hidx : (Subgroup.zpowers (1 : SL(2, ZMod m₆))).index = Nat.card (SL(2, ZMod m₆)) := by
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.index_bot]
      have hfin : (Subgroup.zpowers (1 : SL(2, ZMod m₆))).index ≠ 0 := by
        rw [hidx]
        exact Nat.card_pos.ne'
      rw [← hidx]
      exact stemExtension_pow_index_eq_one' π' hs hc 1 hfin hy hyc
    have hpow := pow_eq_one_of_prod π hπsurj hcent hperf₅ hstem₅ hF₆ hxker hxc
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hpow
    exact hpow

end Torsion
end Ihara
end Inl_A3_CompositeStep
end P2MW.S_Ihara_pow_card_mem_mennickeQ_mul
