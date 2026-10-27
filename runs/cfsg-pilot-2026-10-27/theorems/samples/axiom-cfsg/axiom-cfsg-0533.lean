public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Stellmacher.L3YC

namespace Row13

section Generic

variable {K : Type*} [Group K] [Finite K]

theorem card_sup_eq_two_pow_mul {L S : Subgroup K} (hS2 : IsPGroup 2 S)
    (hSL : S ≤ Subgroup.normalizer (L : Set K)) :
    ∃ n : ℕ, Nat.card ↥(L ⊔ S) = 2 ^ n * Nat.card L := by
  obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hS2 L
  have h1 : L.relIndex (S ⊔ L) = L.relIndex S := B6.relIndex_sup_eq_of_le_normalizer hSL
  have e1 : L.relIndex (S ⊔ L) * Nat.card ↥(L ⊓ (S ⊔ L)) = Nat.card ↥(S ⊔ L) :=
    Subgroup.relIndex_mul_card L (S ⊔ L)
  rw [inf_eq_left.mpr le_sup_right, h1, hn] at e1
  exact ⟨n, by rw [sup_comm, ← e1]⟩

end Generic
end Row13
end Stellmacher.L3YC
end CFSG.Quasithin
end
