@[expose] public section

universe w'' w' w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

namespace Precoverage

variable {J : Precoverage C}

/-- A precoverage is `w`-small, if every `0`-hypercover is `w`-small. -/
class Small (J : Precoverage C) : Prop where
  zeroHypercoverSmall : ∀ {S : C} (E : ZeroHypercover.{max u v} J S), ZeroHypercover.Small.{w'} E

end Precoverage
end CategoryTheory
end
