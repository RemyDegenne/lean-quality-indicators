@[expose] public section

open CategoryTheory Set

universe u v

namespace ProfiniteGrp

/-- The profinite completion of the infinite cyclic group, in any target
universe. -/
abbrev integerCompletion : ProfiniteGrp.{u} :=
  ProfiniteCompletion.completion (GrpCat.of (ULift.{u} (Multiplicative ℤ)))

end ProfiniteGrp
end
