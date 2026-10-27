public section

namespace CFSG.Quasithin

open Module

namespace SteinbergBQ.BinaryPlanes

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem card_mul_card_fixed_le [Finite V] (hV : finrank (ZMod 2) V = 2)
    (S : Set (V →ₗ[ZMod 2] V)) (hS : ∀ s ∈ S, s * s = 1)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) :
    Nat.card S * Nat.card {y : V // ∀ s ∈ S, s y = y} ≤ 4 := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hcardV : Nat.card V = 4 := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), hV, ZMod.card]
    rfl
  by_cases h : ∃ t ∈ S, t ≠ 1
  · obtain ⟨t, htS, ht1⟩ := h
    have hS2 : Nat.card S ≤ 2 := by
      have hsub : S ⊆ ({1, t} : Set (V →ₗ[ZMod 2] V)) := by
        intro s hs
        by_cases hs1 : s = 1
        · exact Or.inl hs1
        · exact Or.inr (involution_eq hV (hS s hs) (hS t htS) (hcomm s hs t htS) hs1 ht1)
      calc Nat.card S ≤ Nat.card ({1, t} : Set (V →ₗ[ZMod 2] V)) :=
            Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
            rw [Nat.card_coe_set_eq]
            exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have hF2 : Nat.card {y : V // ∀ s ∈ S, s y = y} ≤ 2 := by
      refine le_trans ?_ (card_fixed_le hV (hS t htS) ht1)
      refine Nat.card_le_card_of_injective
        (fun y : {y : V // ∀ s ∈ S, s y = y} => (⟨y.1, y.2 t htS⟩ : {y : V // t y = y}))
        fun y z h => Subtype.ext ?_
      exact congrArg (fun u : {y : V // t y = y} => (u : V)) h
    calc Nat.card S * Nat.card {y : V // ∀ s ∈ S, s y = y} ≤ 2 * 2 :=
          Nat.mul_le_mul hS2 hF2
      _ = 4 := rfl
  · push Not at h
    have hS1 : Nat.card S ≤ 1 := by
      calc Nat.card S ≤ Nat.card ({1} : Set (V →ₗ[ZMod 2] V)) :=
            Nat.card_mono (Set.toFinite _) fun s hs => h s hs
        _ = 1 := by rw [Nat.card_coe_set_eq, Set.ncard_singleton]
    have hF4 : Nat.card {y : V // ∀ s ∈ S, s y = y} ≤ 4 := by
      rw [← hcardV]
      exact Nat.card_le_card_of_injective (fun y => y.1) Subtype.val_injective
    calc Nat.card S * Nat.card {y : V // ∀ s ∈ S, s y = y} ≤ 1 * 4 := Nat.mul_le_mul hS1 hF4
      _ = 4 := rfl

end SteinbergBQ.BinaryPlanes
end CFSG.Quasithin
end
