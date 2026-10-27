public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94

open scoped Pointwise

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem mem_Aset {y a : G ⧸ c.G1} {k : G ⧸ c.G2} :
    a ∈ c.Aset y k ↔ c.OnL a k ∧ a ≠ c.x0 ∧ c.Delta.Adj y a :=
  Iff.rfl

end Loc49
end CFSG.Quasithin.H13.AS91
end
