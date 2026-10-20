namespace P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Inl_P2B_M2WAbelian

namespace Ihara

p2m_open

p2m_open

open scoped MatrixGroups commutatorElement

variable (q : ℕ)

p2m_reactivate

p2m_reactivate

variable {E : Type} [Group E]

theorem comap_congFilt_one_commute (π : E →* SL(2, ZMod (q ^ 2)))
    (hsurj : Function.Surjective π) (hcen : MonoidHom.ker π ≤ Subgroup.center E)
    (hq : q.Prime) (hq5 : 5 ≤ q) [NeZero q] :
    ∀ x ∈ (congFilt q 2 1).comap π, ∀ y ∈ (congFilt q 2 1).comap π, Commute x y := by

  set K := congFilt q 2 1 with hKdef
  set W := K.comap π with hW
  have hKW : ∀ a ∈ K, ∃ x ∈ W, π x = a := fun a ha => by
    obtain ⟨x, hx⟩ := hsurj a; exact ⟨x, by simp [hW, Subgroup.mem_comap, hx, ha], hx⟩
  have hβcen : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ∈ Subgroup.center E := fun x hx y hy => by
    apply hcen
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (congFilt_commutative q 2 (by omega) (π x) hx (π y) hy)
  have hliftL : ∀ x ∈ W, ∀ x' ∈ W, π x = π x' → ∀ y ∈ W, ⁅x, y⁆ = ⁅x', y⁆ := by
    intro x hx x' hx' hxx' y hy
    have hc : x'⁻¹ * x ∈ Subgroup.center E := hcen (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel])
    rw [show x = x' * (x'⁻¹ * x) from by group, commutatorElement_mul_central_left hc]
  have hliftR : ∀ x ∈ W, ∀ y ∈ W, ∀ y' ∈ W, π y = π y' → ⁅x, y⁆ = ⁅x, y'⁆ := by
    intro x hx y hy y' hy' hyy'
    rw [← commutatorElement_inv (g₁ := y), hliftL y hy y' hy' hyy' x hx,
      commutatorElement_inv]

  obtain ⟨eE, heEW, heE⟩ := hKW (kE q) (hKdef ▸ kE_mem q)
  obtain ⟨fE, hfEW, hfE⟩ := hKW (kF q) (hKdef ▸ kF_mem q)
  obtain ⟨hE, hhEW, hhE⟩ := hKW (kH q) (hKdef ▸ kH_mem q)

  have hβq : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ^ q = 1 := by
    intro x hx y hy
    rw [← commutatorElement_pow_left_of_central q (hβcen x hx y hy)]
    have hxq : x ^ q ∈ Subgroup.center E := hcen (by
      rw [MonoidHom.mem_ker, map_pow]
      exact congFilt_pow_q_eq_one q 2 (by omega) (Subgroup.mem_comap.mp hx))
    exact commutatorElement_eq_one_iff_commute.mpr
      ((Subgroup.mem_center_iff.mp hxq y).symm)
  have heq1 : ∀ {x : E} {m : ℕ}, Nat.Coprime m q → x ^ m = 1 → x ^ q = 1 → x = 1 := by
    intro x m hco hm hn
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hn)
    rw [hco] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hconj : ∀ (g : SL(2, ZMod (q^2))) {x y x' y' : E}, x ∈ W → y ∈ W →
      x' ∈ W → y' ∈ W → π x' = g * π x * g⁻¹ → π y' = g * π y * g⁻¹ →
      ⁅x', y'⁆ = ⁅x, y⁆ := by
    intro g x y x' y' hx hy hx' hy' hxx' hyy'
    obtain ⟨gE, hgE⟩ := hsurj g
    have hgxW : gE * x * gE⁻¹ ∈ W := Subgroup.mem_comap.mpr (by
      rw [map_mul, map_mul, map_inv, hgE, ← hxx']; exact Subgroup.mem_comap.mp hx')
    have hgyW : gE * y * gE⁻¹ ∈ W := Subgroup.mem_comap.mpr (by
      rw [map_mul, map_mul, map_inv, hgE, ← hyy']; exact Subgroup.mem_comap.mp hy')
    rw [hliftL x' hx' (gE * x * gE⁻¹) hgxW
        (by rw [map_mul, map_mul, map_inv, hgE, hxx']) y' hy',
      hliftR (gE * x * gE⁻¹) hgxW y' hy' (gE * y * gE⁻¹) hgyW
        (by rw [map_mul, map_mul, map_inv, hgE, hyy']),
      commutatorElement_conj_of_central (hβcen x hx y hy)]

  have h2co : Nat.Coprime 2 (q ^ 2) :=
    (Nat.coprime_primes Nat.prime_two hq).mpr (by omega) |>.pow_right 2
  set u2 : (ZMod (q ^ 2))ˣ := ZMod.unitOfCoprime 2 h2co with hu2
  have hu2c : ((u2 : ZMod (q ^ 2)) : ZMod (q ^ 2)) = 2 := ZMod.coe_unitOfCoprime 2 h2co
  have hEH : ⁅eE, hE⁆ = 1 := by
    refine heq1 (m := 3) ((Nat.coprime_primes Nat.prime_three hq).mpr (by omega))
      ?_ (hβq eE heEW hE hhEW)

    have h4 : ⁅eE, hE⁆ ^ 4 = ⁅eE, hE⁆ := by
      rw [← commutatorElement_pow_left_of_central 4 (hβcen eE heEW hE hhEW)]
      refine hconj (hElt u2)⁻¹ heEW hhEW (W.pow_mem heEW 4) hhEW ?_ ?_
      · rw [map_pow, heE, inv_inv,
          show kE q = uElt (R := ZMod (q^2)) q from rfl,
          hElt_inv_mul_uElt_mul_hElt u2 (q : ZMod (q^2)), uElt_pow, hu2c]
        norm_num
      · rw [hhE, inv_inv, hElt_inv_mul_kH_mul_hElt u2]
    have h3 : ⁅eE, hE⁆ ^ 3 * ⁅eE, hE⁆ = 1 * ⁅eE, hE⁆ := by
      rw [← _root_.pow_succ, h4, one_mul]
    exact mul_right_cancel h3

  have hFH : ⁅fE, hE⁆ = 1 := by
    have hwconj : ⁅fE⁻¹, hE⁻¹⁆ = ⁅eE, hE⁆ := by
      refine hconj (weyl2 q) heEW hhEW (W.inv_mem hfEW) (W.inv_mem hhEW) ?_ ?_
      · rw [map_inv, hfE, heE]; exact weyl2_conj_kE.symm
      · rw [map_inv, hhE]; exact weyl2_conj_kH.symm
    rw [commutatorElement_inv_left_of_central (hβcen fE hfEW _ (W.inv_mem hhEW)),
      commutatorElement_inv_right_of_central (hβcen fE hfEW hE hhEW)] at hwconj
    rw [inv_inv] at hwconj
    rw [hwconj, hEH]

  have hEF : ⁅eE, fE⁆ = 1 := by
    refine heq1 (m := 2) ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega))
      ?_ (hβq eE heEW fE hfEW)
    have hwconj : ⁅fE⁻¹, eE⁻¹⁆ = ⁅eE, fE⁆ := by
      refine hconj (weyl2 q) heEW hfEW (W.inv_mem hfEW) (W.inv_mem heEW) ?_ ?_
      · rw [map_inv, hfE, heE]; exact weyl2_conj_kE.symm
      · rw [map_inv, heE, hfE]; exact weyl2_conj_kF.symm
    rw [commutatorElement_inv_left_of_central (hβcen fE hfEW _ (W.inv_mem heEW)),
      commutatorElement_inv_right_of_central (hβcen fE hfEW eE heEW),
      inv_inv, ← commutatorElement_inv] at hwconj
    rw [sq]; nth_rw 1 [← hwconj]; exact inv_mul_cancel _

  have hgen : ∀ a ∈ ({kE q, kF q, kH q} : Set _), ∀ b ∈ ({kE q, kF q, kH q} : Set _),
      ∀ x ∈ W, π x = a → ∀ y ∈ W, π y = b → ⁅x, y⁆ = 1 := by
    intro a ha b hb x hx hxa y hy hyb

    have hsw : ∀ {s : E} {g : SL(2, ZMod (q^2))}, s ∈ W → π s = g →
        ∀ {z : E}, z ∈ W → π z = g → ∀ {w : E}, w ∈ W → ⁅s, w⁆ = ⁅z, w⁆ := by
      intro s g hs hsg z hz hzg w hw
      exact hliftL s hs z hz (hsg.trans hzg.symm) w hw
    have hswR : ∀ {z : E}, z ∈ W → ∀ {s : E} {g : SL(2, ZMod (q^2))}, s ∈ W → π s = g →
        ∀ {w : E}, w ∈ W → π w = g → ⁅z, s⁆ = ⁅z, w⁆ := by
      intro z hz s g hs hsg w hw hwg
      exact hliftR z hz s hs w hw (hsg.trans hwg.symm)
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      [(rw [hsw hx hxa heEW heE hy, hswR heEW hy hyb heEW heE]; simp);
       (rw [hsw hx hxa heEW heE hy, hswR heEW hy hyb hfEW hfE]; exact hEF);
       (rw [hsw hx hxa heEW heE hy, hswR heEW hy hyb hhEW hhE]; exact hEH);
       (rw [hsw hx hxa hfEW hfE hy, hswR hfEW hy hyb heEW heE];
         rw [← _root_.inv_inj, ← commutatorElement_inv] at hEF; simpa using hEF);
       (rw [hsw hx hxa hfEW hfE hy, hswR hfEW hy hyb hfEW hfE]; simp);
       (rw [hsw hx hxa hfEW hfE hy, hswR hfEW hy hyb hhEW hhE]; exact hFH);
       (rw [hsw hx hxa hhEW hhE hy, hswR hhEW hy hyb heEW heE];
         rw [← _root_.inv_inj, ← commutatorElement_inv] at hEH; simpa using hEH);
       (rw [hsw hx hxa hhEW hhE hy, hswR hhEW hy hyb hfEW hfE];
         rw [← _root_.inv_inj, ← commutatorElement_inv] at hFH; simpa using hFH);
       (rw [hsw hx hxa hhEW hhE hy, hswR hhEW hy hyb hhEW hhE]; simp)]

  have hK : K = Subgroup.closure {kE q, kF q, kH q} := hKdef ▸ congFilt_one_eq_closure_efh q
  intro x hx y hy
  rw [show (Commute x y ↔ ⁅x, y⁆ = 1) from commutatorElement_eq_one_iff_commute.symm]
  have hxK : π x ∈ Subgroup.closure {kE q, kF q, kH q} := hK ▸ hx
  have hyK : π y ∈ Subgroup.closure {kE q, kF q, kH q} := hK ▸ hy

  let P : (a b : SL(2, ZMod (q^2))) →
      a ∈ Subgroup.closure {kE q, kF q, kH q} →
      b ∈ Subgroup.closure {kE q, kF q, kH q} → Prop :=
    fun a b _ _ => ∀ x ∈ W, π x = a → ∀ y ∈ W, π y = b → ⁅x, y⁆ = 1
  suffices h : P (π x) (π y) hxK hyK from h x hx rfl y hy rfl
  refine Subgroup.closure_induction₂ (p := P) (fun a b ha hb => hgen a ha b hb)
    ?_ ?_ ?_ ?_ ?_ ?_ hxK hyK
  ·
    intro b _ x' hx' hx1 y' hy' _
    exact (commutatorElement_eq_one_iff_commute.mpr
      ((Subgroup.mem_center_iff.mp (hcen (π.mem_ker.mpr hx1)) y').symm))
  ·
    intro a _ x' _ _ y' _ hy1
    exact (commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp (hcen (π.mem_ker.mpr hy1)) x'))
  ·
    intro a b c ha hb hc Pac Pbc x' hx' hxab y' hy' hyc
    obtain ⟨xa, hxaW, hxa⟩ := hKW a (hK ▸ ha)
    obtain ⟨xb, hxbW, hxb⟩ := hKW b (hK ▸ hb)
    rw [hliftL x' hx' (xa * xb) (W.mul_mem hxaW hxbW)
        (by rw [map_mul, hxa, hxb, hxab]) y' hy',
      commutatorElement_mul_left_of_central (hβcen xb hxbW y' hy'),
      Pac xa hxaW hxa y' hy' hyc, Pbc xb hxbW hxb y' hy' hyc, one_mul]
  ·
    intro b c a hb hc ha Pab Pac x' hx' hxa y' hy' hybc
    obtain ⟨yb, hybW, hyb⟩ := hKW b (hK ▸ hb)
    obtain ⟨yc, hycW, hyc⟩ := hKW c (hK ▸ hc)
    rw [hliftR x' hx' y' hy' (yb * yc) (W.mul_mem hybW hycW)
        (by rw [map_mul, hyb, hyc, hybc]),
      commutatorElement_mul_right_of_central (hβcen x' hx' yc hycW),
      Pab x' hx' hxa yb hybW hyb, Pac x' hx' hxa yc hycW hyc, one_mul]
  ·
    intro a b ha hb Pab x' hx' hxa y' hy' hyb
    obtain ⟨xa, hxaW, hxaE⟩ := hKW a (hK ▸ ha)
    rw [hliftL x' hx' xa⁻¹ (W.inv_mem hxaW)
        (by rw [map_inv, hxaE, hxa]) y' hy',
      commutatorElement_inv_left_of_central (hβcen xa hxaW y' hy'),
      Pab xa hxaW hxaE y' hy' hyb, inv_one]
  ·
    intro a b ha hb Pab x' hx' hxa y' hy' hyb
    obtain ⟨yb', hybW, hybE⟩ := hKW b (hK ▸ hb)
    rw [hliftR x' hx' y' hy' yb'⁻¹ (W.inv_mem hybW)
        (by rw [map_inv, hybE, hyb]),
      commutatorElement_inv_right_of_central (hβcen x' hx' yb' hybW),
      Pab x' hx' hxa yb' hybW hybE, inv_one]

end Ihara
end Inl_P2B_M2WAbelian
end P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute
