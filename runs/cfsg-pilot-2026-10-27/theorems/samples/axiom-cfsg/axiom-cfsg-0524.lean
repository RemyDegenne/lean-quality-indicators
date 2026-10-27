public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.H

section Br

variable {G : Type} [Group G] [Finite G]

theorem card_star_quot_le_cs5 {H I M : Subgroup G} (hIH : I ≤ H)
    (hker : kerIn (M ⊓ I) I = pCoreOf 2 I) :
    Nat.card (↥(E2.star (H ⊓ M) H I) ⧸
        (E2.star (H ⊓ M) H (pCoreOf 2 I)).subgroupOf (E2.star (H ⊓ M) H I)) ≤
      Nat.card (E2.StarQuot (M ⊓ I) I) := by
  let π : ↥H →* E2.StarQuot (H ⊓ M) H := QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)
  have hmem : ∀ a : ↥I, π ⟨a, hIH a.2⟩ ∈ E2.star (H ⊓ M) H I := fun a =>
    mem_star_cs5.mpr ⟨⟨a, hIH a.2⟩, a.2, rfl⟩
  let f : ↥I → (↥(E2.star (H ⊓ M) H I) ⧸
      (E2.star (H ⊓ M) H (pCoreOf 2 I)).subgroupOf (E2.star (H ⊓ M) H I)) := fun a =>
    QuotientGroup.mk ⟨π ⟨a, hIH a.2⟩, hmem a⟩
  have hf : ∀ a b : ↥I, QuotientGroup.leftRel ((kerIn (M ⊓ I) I).subgroupOf I) a b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf, hker] at hab
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    show (π ⟨a, hIH a.2⟩)⁻¹ * π ⟨b, hIH b.2⟩ ∈ E2.star (H ⊓ M) H (pCoreOf 2 I)
    refine mem_star_cs5.mpr ⟨⟨(a : G)⁻¹ * b, H.mul_mem (H.inv_mem (hIH a.2)) (hIH b.2)⟩, ?_, ?_⟩
    · simpa using hab
    · have e : (⟨(a : G)⁻¹ * b, H.mul_mem (H.inv_mem (hIH a.2)) (hIH b.2)⟩ : ↥H) =
          (⟨a, hIH a.2⟩ : ↥H)⁻¹ * ⟨b, hIH b.2⟩ := rfl
      show (QuotientGroup.mk (⟨(a : G)⁻¹ * b, H.mul_mem (H.inv_mem (hIH a.2)) (hIH b.2)⟩ : ↥H) :
        E2.StarQuot (H ⊓ M) H) = (π ⟨a, hIH a.2⟩)⁻¹ * π ⟨b, hIH b.2⟩
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rfl
  let ψ : (↥I ⧸ (kerIn (M ⊓ I) I).subgroupOf I) → (↥(E2.star (H ⊓ M) H I) ⧸
      (E2.star (H ⊓ M) H (pCoreOf 2 I)).subgroupOf (E2.star (H ⊓ M) H I)) :=
    Quotient.lift f hf
  have hψ : Function.Surjective ψ := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H y₀ =>
      obtain ⟨a, ha, hay⟩ := mem_star_cs5.mp y₀.2
      refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
      show f ⟨a, ha⟩ = QuotientGroup.mk y₀
      exact congrArg QuotientGroup.mk (Subtype.ext hay)
  exact Nat.card_le_card_of_surjective ψ hψ

end Br
end CFSG.Quasithin.H13
end
