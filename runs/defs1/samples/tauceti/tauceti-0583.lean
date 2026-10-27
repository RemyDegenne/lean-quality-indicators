public section

open Polynomial

open scoped IntermediateField

namespace TauCeti.GenusDrop

variable (p : ℕ) [hp : Fact p.Prime]

/-- `y = w ^ p`. -/
noncomputable def genY : RatFunc (RatFunc (ZMod p)) :=
  RatFunc.X ^ p

end TauCeti.GenusDrop
end
