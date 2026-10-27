public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

namespace ToralCensus

open LinearFlag

theorem card_multiplicative_zmod_eq (k : ℕ) : Nat.card (Multiplicative (ZMod k)) = k := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

end ToralCensus
end CFSG.AGLEmbedding
end
