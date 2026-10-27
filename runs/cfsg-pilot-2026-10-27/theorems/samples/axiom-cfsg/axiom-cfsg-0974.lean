public section

namespace CFSG.RankThree.PartTwo.Sec3

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G]

section SectionCase

variable [Finite G] {Q B : Subgroup G} [Q.Normal]
  (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB3 : ∀ b ∈ B, b ^ 3 = 1) (hB9 : Nat.card B = 9)
  (htr : ∀ d ∈ B, ∀ d' ∈ B, d ≠ 1 → d' ≠ 1 → ∃ n ∈ normalizer (B : Set G), n * d * n⁻¹ = d')

include hBc hB3 hB9 htr

omit [Finite G] [Q.Normal] hBc hB3 hB9 htr in
theorem card_map_le_card [Finite G] {H : Type*} [Group H] (f : G →* H) (K : Subgroup G) :
    Nat.card (K.map f) ≤ Nat.card K := by
  refine Nat.card_le_card_of_surjective (fun x : K => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ :
    K.map f)) ?_
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

end SectionCase
end CFSG.RankThree.PartTwo.Sec3
end
