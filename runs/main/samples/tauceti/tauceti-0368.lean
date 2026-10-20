public section

universe v

namespace TauCeti.SpStd

open scoped CategoryTheory.MonObj

variable (n : ℕ)

section Carrier

open AlgebraicGeometry CategoryTheory

theorem groupScheme_def :
    groupScheme n =
      CommHopfAlgCat.quotientSpec
        (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
        (definingIdeal n) := by
  rw [groupScheme, definingIdeal]

end Carrier
end TauCeti.SpStd
end
