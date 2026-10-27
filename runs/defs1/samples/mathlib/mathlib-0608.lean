@[expose] public section

universe w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/-- The associated pre-`0`-hypercover family to a precoverage. -/
@[simps]
def Precoverage.preZeroHypercoverFamily (K : Precoverage C) :
    PreZeroHypercoverFamily C where
  property X E := E.presieve₀ ∈ K X
  iff_shrink {X} E := by simp

end CategoryTheory
end
