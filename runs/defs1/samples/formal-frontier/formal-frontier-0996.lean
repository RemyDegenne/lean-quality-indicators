@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp

namespace MaximalProPQuotient

variable (p : ℕ) [Fact p.Prime] (G : ProfiniteGrp.{u})

namespace Quotient

/-- Intersections of pro-`p` quotient kernels are again pro-`p` quotient
kernels. -/
def inf (U V : Quotient p G) : Quotient p G where
  toOpenNormalSubgroup := U.toOpenNormalSubgroup ⊓ V.toOpenNormalSubgroup
  isPGroup' := quotient_inf_isPGroup p G U V

end Quotient
end MaximalProPQuotient
end ProfiniteGrp
end
