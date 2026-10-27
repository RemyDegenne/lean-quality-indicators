public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank

open CFSG.ComponentClassification.RankTwoStandard

open scoped MatrixGroups

section Center

variable {A : Type} [Group A] [Finite A]

theorem exists_double_cover {E Q : Type} [Group E] [Finite E] [Group.IsPerfect E] [Group Q]
    (η : E →* Q) (hsurj : Function.Surjective η) (hcen : η.ker ≤ center E)
    (hp : IsPGroup 2 η.ker) (hne : η.ker ≠ ⊥) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (Z : Subgroup Y) (_ : Z.Normal),
      Z ≤ center Y ∧ Nat.card Z = 2 ∧ Z ≤ commutator Y ∧ Nonempty (Y ⧸ Z ≃* Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := η.ker with hPdef
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne ((card_eq_one).mp (by rw [hk, pow_zero]))
  obtain ⟨W', hW'⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) 2 (n := k - 1)
    (by rw [hk]; exact pow_dvd_pow 2 (Nat.sub_le k 1))
  set W : Subgroup E := W'.map P.subtype with hWdef
  have hWP : W ≤ P := map_subtype_le W'
  have hWc : W ≤ center E := hWP.trans hcen
  have hWn : W.Normal := ⟨fun w hw g => by
    rw [mem_center_iff.mp (hWc hw) g, mul_inv_cancel_right]
    exact hw⟩
  have hWcard : Nat.card W = 2 ^ (k - 1) := by
    rw [hWdef, card_map_of_injective P.subtype_injective, hW']
  set Z : Subgroup (E ⧸ W) := P.map (QuotientGroup.mk' W) with hZdef
  have hZn : Z.Normal := (MonoidHom.normal_ker η).map _ (QuotientGroup.mk'_surjective W)
  have hZcard : Nat.card Z = 2 := by
    let f : P →* E ⧸ W := (QuotientGroup.mk' W).comp P.subtype
    have hrange : f.range = Z := by rw [MonoidHom.range_comp, range_subtype]
    have hfker : f.ker = W.subgroupOf P := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      change QuotientGroup.mk' W (x : E) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h1 := card_ker_mul_card_range f
    rw [hrange, hfker, Nat.card_congr (subgroupOfEquivOfLe hWP).toEquiv, hWcard, hk] at h1
    have h2 : 2 ^ k = 2 ^ (k - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hZc : Z ≤ center (E ⧸ W) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W g
    rw [← map_mul, ← map_mul, mem_center_iff.mp (hcen hc) g]
  have hperf : commutator (E ⧸ W) = ⊤ :=
    commutator_eq_top_of_surjective (QuotientGroup.mk'_surjective W)
      Group.IsPerfect.commutator_eq_top
  refine ⟨E ⧸ W, inferInstance, inferInstance, Z, hZn, hZc, hZcard, hperf ▸ le_top,
    ⟨(QuotientGroup.quotientQuotientEquivQuotient W P hWP).trans
      (QuotientGroup.quotientKerEquivOfSurjective η hsurj)⟩⟩

end Center
end CFSG.ComponentClassification.GMS78
end
