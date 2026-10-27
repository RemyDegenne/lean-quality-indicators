public section

namespace CFSG.Quasithin.H13.A5.SzPair

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

variable {T K K₁ : Subgroup G}

section Counting

variable [Finite G]

theorem card_le_two_mul (h : PairFacts T K K₁) {A : Subgroup G} (hAT : A ≤ T) {a : G}
    (haA : a ∈ A) (haN : a ∉ Subgroup.normalizer (K : Set G)) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (K : Set G)) := by
  classical
  let f : ↥A → ↥(A ⊓ Subgroup.normalizer (K : Set G)) × Bool := fun b =>
    if hb : (b : G) ∈ Subgroup.normalizer (K : Set G) then (⟨b, b.2, hb⟩, true)
    else (⟨a * b, A.mul_mem haA b.2, h.mul_mem_normalizer (hAT haA) haN (hAT b.2) hb⟩, false)
  have hf : Function.Injective f := by
    intro b b' hbb
    by_cases hb : (b : G) ∈ Subgroup.normalizer (K : Set G) <;>
      by_cases hb' : (b' : G) ∈ Subgroup.normalizer (K : Set G)
    · simp only [f, hb, hb', dite_true, Prod.mk.injEq] at hbb
      exact Subtype.ext
        (congrArg (fun x : ↥(A ⊓ Subgroup.normalizer (K : Set G)) => (x : G)) hbb.1)
    · simp [f, hb, hb'] at hbb
    · simp [f, hb, hb'] at hbb
    · simp only [f, hb, hb', dite_false, Prod.mk.injEq] at hbb
      exact Subtype.ext (mul_left_cancel
        (congrArg (fun x : ↥(A ⊓ Subgroup.normalizer (K : Set G)) => (x : G)) hbb.1))
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  omega

end Counting
end CFSG.Quasithin.H13.A5.SzPair
end
