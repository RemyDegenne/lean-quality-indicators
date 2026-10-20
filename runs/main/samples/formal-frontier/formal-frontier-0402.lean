@[expose] public section

universe u v

open scoped Cardinal

namespace GroupLike

variable (R : Type u) (C : Type v)

variable [CommRing R] [IsDomain R] [AddCommGroup C] [Module R C] [Coalgebra R C]
  [Module.IsTorsionFree R C]

theorem nat_card_le_finrank_of_rank_lt_aleph0 (hrank : Module.rank R C < ℵ₀) :
    Nat.card (GroupLike R C) ≤ Module.finrank R C :=
  Cardinal.toNat_le_toNat (cardinalMk_le_rank R C) hrank

end GroupLike
end
