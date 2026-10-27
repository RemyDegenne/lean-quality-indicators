@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp

namespace MaximalProPQuotient

variable (p : ℕ) [Fact p.Prime] (G : ProfiniteGrp.{u})

namespace Quotient

/-- The trivial quotient is a `p`-group quotient. -/
def top : Quotient p G where
  toOpenNormalSubgroup := topOpenNormal G
  isPGroup' := by
    change IsPGroup p (G ⧸ (⊤ : Subgroup G))
    let _ : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
      QuotientGroup.subsingleton_quotient_top
    exact IsPGroup.of_subsingleton p (G ⧸ (⊤ : Subgroup G))

end Quotient
end MaximalProPQuotient
end ProfiniteGrp
end
