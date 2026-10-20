public section

open CategoryTheory Limits

namespace TopModuleCat

universe v u

variable {R : Type u} [Ring R] [TopologicalSpace R]

theorem restrictScalarsInt_map_hom {M N : TopModuleCat.{v} R} (f : M ⟶ N) :
    (restrictScalarsInt.map f).hom = f.hom.restrictScalars ℤ :=
  (rfl)

end TopModuleCat
end
