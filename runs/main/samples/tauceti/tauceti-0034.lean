public section

open Equiv FundamentalGroup

namespace TauCeti

open ThricePuncturedSphere PermutationTriple TriangleGroup

variable {n : ℕ}

namespace ConnectedFiberNumberedCover

variable (c : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n)

theorem isRegular_iff_card_deck :
    (c.connectedTriple : PermutationTriple n).IsRegular ↔ Nat.card (deck ⇑c.cover.proj) = n := by
  rw [isRegular_iff_card_automorphismGroup, and_iff_right c.connectedTriple.2,
    Nat.card_congr c.deckMulEquiv.toEquiv]

end ConnectedFiberNumberedCover
end TauCeti
end
