public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser

variable {G : Type*} [Group G] [Finite G]

namespace Cfg

variable {j : ℕ} (c : Cfg G j)

theorem card_J_ne_one : Nat.card c.J ≠ 1 := fun h => c.J_ne_bot (Subgroup.eq_bot_of_card_eq _ h)

end Cfg
end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser
end
