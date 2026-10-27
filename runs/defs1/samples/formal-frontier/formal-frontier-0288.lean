@[expose] public section

universe uR uM

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

open scoped ZeroObject

namespace ModuleCat

variable (R : Type uR) [Ring R]

namespace Stable

/-- The additive quotient functor from modules to their stable category. -/
abbrev quotient : ModuleCat.{uM} R ⥤ Stable.{uR, uM} R :=
  CategoryTheory.Quotient.functor (stableHomRel R)

end Stable
end ModuleCat
end
