public section

namespace TauCeti.DynkinType

open Function

open scoped _root_.Matrix

@[simp] theorem f4SpecialIsogenyTorusMap_apply_apply
    {A : Type*} [CommRing A] (s : Fin 4 → Aˣ) :
    f4SpecialIsogenyTorusMap (f4SpecialIsogenyTorusMap s) =
      fun i => s i ^ 2 := by
  ext i
  fin_cases i <;> simp [f4SpecialIsogenyTorusMap]

end TauCeti.DynkinType
end
