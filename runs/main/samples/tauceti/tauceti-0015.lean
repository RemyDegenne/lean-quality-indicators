public section

open CategoryTheory WithConv

open scoped Matrix TensorProduct

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

universe u

noncomputable section

variable (k : Type u) [CommRing k] [Algebra (ZMod 2) k]

theorem coordinateMap_def :
    coordinateMap k =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso (ZMod 2) k 26).inv ≫
        CommHopfAlgCat.baseChangeMap (K := k)
          (CommHopfAlgCat.mkQuotient
            (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26) definingIdeal) := by
  rw [coordinateMap]

end
end TauCeti.F4ShortRoot.PrimeField
end
