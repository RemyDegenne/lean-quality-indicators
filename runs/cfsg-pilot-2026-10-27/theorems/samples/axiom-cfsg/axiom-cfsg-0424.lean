public section

open scoped BigOperators Classical

namespace CFSG.SmallDefect

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Fintype G]

theorem blocksInnerProduct_sub_sub {X : Type} [Group X] [Fintype X] {a b c d : X → ℂ}
    (ha : a ∈ BlocksIrr X) (hb : b ∈ BlocksIrr X) (hc : c ∈ BlocksIrr X)
    (hd : d ∈ BlocksIrr X) :
    BlocksInnerProduct (a - b) (c - d) =
      (if a = c then 1 else 0) - (if a = d then 1 else 0) - (if b = c then 1 else 0) +
        (if b = d then 1 else 0) := by
  have h := blocksInnerProduct_irreducible_differences ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩
  simpa only [Subtype.mk.injEq] using h

end CFSG.SmallDefect
end
