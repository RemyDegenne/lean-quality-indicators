public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_complement_of_central_sylow {Q X : Subgroup G}
    (hQX : Q ≤ X) (hQ : IsPGroup p Q)
    (hcent : ∀ x ∈ X, ∀ q ∈ Q, x * q = q * x)
    (hidx : ¬ p ∣ Q.relIndex X) :
    ∃ O : Subgroup G, O ≤ X ∧ (∀ x ∈ X, x ∈ O ↔ ¬ p ∣ orderOf x) ∧ Q ⊓ O = ⊥ ∧
      ∀ x ∈ X, ∃ q ∈ Q, ∃ o ∈ O, x = q * o := by
  have hQp : IsPGroup p (Q.subgroupOf X) := hQ.comap_subtype
  have hidx' : ¬ p ∣ (Q.subgroupOf X).index := hidx
  let P : Sylow p X := hQp.toSylow hidx'
  have hP : (P : Subgroup X) = Q.subgroupOf X := IsPGroup.toSylow_coe hQp hidx'
  have hcentP : Subgroup.centralizer (P : Set X) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : q ∈ Q.subgroupOf X := (IsPGroup.mem_toSylow hQp hidx').mp hq
    have hqQ : ((q : X) : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq'
    exact Subtype.ext (hcent (x : X) x.2 (q : X) hqQ).symm
  have hnorm : Subgroup.normalizer (P : Set X) ≤ Subgroup.centralizer (P : Set X) := by
    rw [hcentP]
    exact le_top
  obtain ⟨K, hKn, hKp, hKidx, -, -, hcompl, -, hKinf, -, -⟩ :=
    burnside_normal_complement P hnorm
  letI : K.Normal := hKn
  let O : Subgroup G := K.map X.subtype
  have hOX : O ≤ X := Subgroup.map_subtype_le K
  have hmemO : ∀ {x : G} (hx : x ∈ X), x ∈ O ↔ (⟨x, hx⟩ : X) ∈ K := by
    intro x hx
    rw [show O = K.map X.subtype from rfl, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hy' : y = (⟨x, hx⟩ : X) := Subtype.ext hyx
      rwa [hy'] at hy
    · intro hxK
      exact ⟨(⟨x, hx⟩ : X), hxK, rfl⟩
  have hpow : IsPGroup p (X ⧸ K) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [← Subgroup.index_eq_card, hKidx]
    exact hn
  have hcase : ∀ x ∈ X, x ∈ O ↔ ¬ p ∣ orderOf x := by
    intro x hx
    rw [hmemO hx]
    constructor
    · intro hxK hp
      apply hKp
      have hy : orderOf (⟨⟨x, hx⟩, hxK⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
      have h1 : orderOf (⟨⟨x, hx⟩, hxK⟩ : K) = orderOf (⟨x, hx⟩ : X) :=
        Subgroup.orderOf_mk (⟨x, hx⟩ : X) hxK
      have h2 : orderOf (⟨x, hx⟩ : X) = orderOf x := Subgroup.orderOf_mk x hx
      rw [h1, h2] at hy
      exact hp.trans hy
    · intro hxnot
      have hmapdvd :
          orderOf (QuotientGroup.mk' K (⟨x, hx⟩ : X)) ∣ orderOf (⟨x, hx⟩ : X) :=
        orderOf_map_dvd (QuotientGroup.mk' K) (⟨x, hx⟩ : X)
      have hmapnot : ¬ p ∣ orderOf (QuotientGroup.mk' K (⟨x, hx⟩ : X)) := by
        intro hp
        apply hxnot
        rw [← Subgroup.orderOf_mk x hx]
        exact hp.trans hmapdvd
      have hone : QuotientGroup.mk' K (⟨x, hx⟩ : X) = 1 := by
        by_contra hne
        exact hmapnot (hpow.dvd_orderOf hne)
      exact (QuotientGroup.eq_one_iff (⟨x, hx⟩ : X)).mp hone
  have hinf : Q ⊓ O = ⊥ := by
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨hyQ, hyO⟩ := Subgroup.mem_inf.mp hy
    have hyX : y ∈ X := hQX hyQ
    have hyK : (⟨y, hyX⟩ : X) ∈ K := (hmemO hyX).mp hyO
    have hyQ' : (⟨y, hyX⟩ : X) ∈ Q.subgroupOf X := by
      rwa [Subgroup.mem_subgroupOf]
    have hbot : (⟨y, hyX⟩ : X) ∈ K ⊓ Q.subgroupOf X := ⟨hyK, hyQ'⟩
    rw [← hP, hKinf, Subgroup.mem_bot] at hbot
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hbot)
  refine ⟨O, hOX, hcase, hinf, ?_⟩
  intro x hx
  obtain ⟨⟨q, o⟩, hqo, -⟩ := hcompl.symm.existsUnique (⟨x, hx⟩ : X)
  refine ⟨((q : X) : G), ?_, ((o : X) : G), ?_, ?_⟩
  · have hqQ : (q : X) ∈ Q.subgroupOf X := by
      rw [← hP]
      exact q.2
    exact Subgroup.mem_subgroupOf.mp hqQ
  · exact Subgroup.mem_map_of_mem X.subtype o.2
  · exact (congrArg Subtype.val hqo).symm

end CFSG.GroupTheory
end
