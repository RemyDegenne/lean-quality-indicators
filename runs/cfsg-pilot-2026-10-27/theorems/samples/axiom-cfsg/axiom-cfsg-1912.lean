public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LinearGroups

open scoped MatrixGroups commutatorElement

open A1c

section Main3

variable {L : Type*} [Group L] [Finite L]

theorem two_lt_pRank_of_quotient_sl2_three (P : Subgroup L) [P.Normal]
    (hP : IsPOnePlusTwo 3 ↥P) (hL : Nonempty (L ⧸ P ≃* SL(2, ZMod 3))) {t : L}
    (ht2 : orderOf t = 2) (htP : ∃ y ∈ P, t * y * t⁻¹ ≠ y) {X : Subgroup L}
    (hXcard : Nat.card X = 3) (hXt : X ≤ Subgroup.centralizer ({t} : Set L))
    (hXZ : X ≠ Subgroup.center L) : 2 < pRank 3 (⊤ : Subgroup L) := by
  classical
  obtain ⟨e⟩ := hL
  let π : L →* SL(2, ZMod 3) := e.toMonoidHom.comp (QuotientGroup.mk' P)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective P)
  have hker : π.ker = P := by
    ext g
    rw [MonoidHom.mem_ker]
    show e (g : L ⧸ P) = 1 ↔ g ∈ P
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hP' := hP
  obtain ⟨hext, hPcard, hPexp⟩ := hP
  have := hext
  have hPp : ∀ y ∈ P, y ^ 3 = 1 := fun y hy => by
    simpa using congrArg Subtype.val (hPexp ⟨y, hy⟩)
  set Z := centerOf P with hZdef
  have hZP : Z ≤ P := inf_le_left
  have hZcard : Nat.card Z = 3 := card_centerOf hext
  have hZexp : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => hPp z (hZP hz)
  have hπP : ∀ y ∈ P, π y = 1 := fun y hy => by
    rw [← MonoidHom.mem_ker, hker]; exact hy
  have hπmem : ∀ y, π y = 1 → y ∈ P := fun y hy => by
    rw [← hker]; exact hy
  have hZcen : ∀ g : L, ∀ z ∈ Z, g * z = z * g := by
    have := centerOf_normal (P := P)
    have hcyc : IsCyclic ↥Z := isCyclic_of_prime_card hZcard
    let ψ : L →* MulAut ↥Z := MulAut.conjNormal
    have hMA : ∀ a : MulAut ↥Z, a * a = 1 := by
      intro a
      have h1 : Nat.card (MulAut ↥Z) = 2 := by
        rw [IsCyclic.card_mulAut, hZcard, Nat.totient_prime Nat.prime_three]
      have : Finite (MulAut ↥Z) := Nat.finite_of_card_ne_zero (by rw [h1]; norm_num)
      have h2 := pow_card_eq_one' (G := MulAut ↥Z) (x := a)
      rw [h1, sq] at h2
      exact h2
    have hψ : ψ = 1 := hom_eq_one_of_sl2_three π hπ hMA ψ (by
      intro k hk
      rw [hker] at hk
      rw [MonoidHom.mem_ker]
      ext w
      have h1 := (mem_centerOf_iff.1 w.2).2 k hk
      have h2 : (((MulAut.conjNormal k : MulAut ↥Z) w : ↥Z) : L) = k * w * k⁻¹ :=
        MulAut.conjNormal_apply k w
      show (((MulAut.conjNormal k : MulAut ↥Z) w : ↥Z) : L) = (w : L)
      rw [h2, mul_inv_eq_iff_eq_mul]
      exact h1)
    intro g z hz
    have hψg : ψ g = 1 := by rw [hψ]; rfl
    have h3 := congrArg (fun φ : MulAut ↥Z => ((φ ⟨z, hz⟩ : ↥Z) : L)) hψg
    have h2 : (((MulAut.conjNormal g : MulAut ↥Z) ⟨z, hz⟩ : ↥Z) : L) = g * z * g⁻¹ :=
      MulAut.conjNormal_apply g ⟨z, hz⟩
    have h4 : g * z * g⁻¹ = z := by
      have h5 : (((MulAut.conjNormal g : MulAut ↥Z) ⟨z, hz⟩ : ↥Z) : L) = z := h3
      rw [← h2]; exact h5
    rw [mul_inv_eq_iff_eq_mul] at h4
    exact h4
  obtain ⟨Θ, hΘ1, hΘneg⟩ := exists_actGL (p := 3) hP'
  have hPK : ∀ y ∈ P, Θ y = 1 := fun y hy =>
    (hΘ1 y).2 fun y' hy' => commutator_mem_centerOf hext hy hy'
  have hdet : ∀ g : L, ((Θ g : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
    have hf : (Matrix.GeneralLinearGroup.det.comp Θ) = 1 :=
      hom_eq_one_of_sl2_three π hπ (fun a => by revert a; decide) _ (by
        intro k hk
        rw [hker] at hk
        rw [MonoidHom.mem_ker]
        simp [hPK k hk])
    intro g
    have := congrArg (fun f : L →* (ZMod 3)ˣ => ((f g : (ZMod 3)ˣ) : ZMod 3)) hf
    simpa using this
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have htt : t * t = 1 := by rw [← sq]; exact ht2 ▸ pow_orderOf_eq_one t
  have hΘt1 : Θ t ≠ 1 := by
    intro h
    obtain ⟨y, hyP, hy⟩ := htP
    apply hy
    have hall := (hΘ1 t).1 h y hyP
    set z := t * y * t⁻¹ * y⁻¹ with hz
    have hzy : t * y * t⁻¹ = z * y := by rw [hz]; group
    have h1 : t * (t * y * t⁻¹) * t⁻¹ = y := by
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
        _ = y := by rw [htt]; group
    have h3 : t * (t * y * t⁻¹) * t⁻¹ = z * (z * y) := by
      rw [hzy]
      calc t * (z * y) * t⁻¹ = (t * z * t⁻¹) * (t * y * t⁻¹) := by group
        _ = z * (z * y) := by rw [mul_inv_eq_iff_eq_mul.2 (hZcen t z hall), hzy]
    have h4 : z * z = 1 := by
      have h5 : z * z * y = 1 * y := by
        calc z * z * y = z * (z * y) := by group
          _ = y := by rw [← h3, h1]
          _ = 1 * y := (one_mul y).symm
      exact mul_right_cancel h5
    have hz1 : z = 1 := by
      calc z = z ^ 3 * (z * z)⁻¹ := by group
        _ = 1 := by rw [hZexp z hall, h4]; simp
    rw [hz1, one_mul] at hzy
    exact hzy
  have hΘt : Θ t = -1 := by
    rcases GL2_eq_one_or_neg_one_of_sq_eq_one h2 (by rw [← map_mul, htt, map_one]) (hdet t) with h | h
    · exact absurd h hΘt1
    · exact h
  have ht : ∀ y ∈ P, t * y * t⁻¹ * y ∈ Z := (hΘneg t).1 hΘt
  have hπt : π t = sl2NegOne 3 := by
    apply sl2_eq_negOne_of_sq_eq_one_three (by rw [← map_mul, htt, map_one])
    intro h1
    have htP' : t ∈ P := hπmem t h1
    have h3 : t ^ 3 = 1 := hPp t htP'
    have h4 : t = 1 := by
      calc t = t ^ 3 * (t * t)⁻¹ := by group
        _ = 1 := by rw [h3, htt]; simp
    rw [h4, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hcenterL : Subgroup.center L ≤ Z := by
    intro z hz
    have hzc : ∀ g : L, g * z = z * g := Subgroup.mem_center_iff.1 hz
    have hπzc : π z ∈ Subgroup.center (SL(2, ZMod 3)) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨g, rfl⟩ := hπ s
      rw [← map_mul, ← map_mul, hzc g]
    rcases eq_one_or_eq_sl2NegOne_of_mem_center hπzc with h | h
    · exact ⟨hπmem z h, Subgroup.mem_centralizer_iff.2 fun y hy => hzc y⟩
    · exfalso
      have hztP : z * t⁻¹ ∈ P := by
        apply hπmem
        rw [map_mul, map_inv, h, hπt, mul_inv_cancel]
      have hΘz : Θ z = 1 := (hΘ1 z).2 fun y hy => by
        have : z * y * z⁻¹ * y⁻¹ = 1 := by rw [← hzc y]; group
        rw [this]; exact (centerOf P).one_mem
      have hΘz' : Θ z = -1 := by
        have : z = (z * t⁻¹) * t := by group
        rw [this, map_mul, hPK _ hztP, one_mul, hΘt]
      exact neg_one_ne_one_GL_three (hΘz'.symm.trans hΘz)
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 (by rw [hXcard])
  set x : L := (x' : L) with hxdef
  have hxX : x ∈ X := x'.2
  have hxp : orderOf x = 3 := by rw [hxdef, Subgroup.orderOf_coe, hx']
  have hxcent : x ∈ Subgroup.centralizer ({t} : Set L) := hXt hxX
  have hxt : t * x = x * t := Subgroup.mem_centralizer_iff.1 hxcent t (Set.mem_singleton t)
  by_cases hΘx : Θ x = 1
  ·
    have hxall := (hΘ1 x).1 hΘx
    have hxc : ∀ y ∈ P, x * y = y * x := fun y hy => by
      have h1 := comm_eq_one_of_inverting hp2 hPp hy (fun z hz => hZcen t z hz)
        (fun z hz => hZcen x z hz) hxt (ht y hy) (hxall y hy)
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hxP : x ∉ P := by
      intro hxPm
      have hxZ : x ∈ Z := (mem_centerOf_iff).2 ⟨hxPm, fun y hy => (hxc y hy).symm⟩
      have h1 : Subgroup.zpowers x = X :=
        Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hxX)
          (by rw [Nat.card_zpowers, hxp, hXcard])
      have h2 : Subgroup.zpowers x = Z := zpowers_eq_of_card_eq_prime hZcard hxZ hxp
      apply hXZ
      rw [← h1, h2]
      exact le_antisymm hcenterL (fun z hz => Subgroup.mem_center_iff.2 fun g => hZcen g z hz)
        |>.symm
    exact two_lt_pRank_of_centralizing_element hP' hxp hxc hxP
  ·
    have hxV : ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ Z := by
      by_contra hcon
      push Not at hcon
      exact hΘx ((hΘ1 x).2 hcon)
    exact two_lt_pRank_of_inverting_element hp2 hP' ht hxcent hxp hxV

end Main3
end CFSG.Quasithin
end
