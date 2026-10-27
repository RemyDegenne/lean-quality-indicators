public section

namespace TauCeti

open Matrix

universe u

variable (m : Type*) [Fintype m] [LinearOrder m] (R : Type u)

section Ring

variable [Ring R]

/-- The upper-unitriangular subgroup of `GLₘ(R)` for a finite linearly ordered index type `m`. -/
def upperUnitriangularGroup : Subgroup (GL m R) where
  carrier := {g | (g : Matrix m m R).IsUpperUnitriangular}
  one_mem' := Matrix.isUpperUnitriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa only [Set.mem_ofPred_eq, Units.val_mul, Matrix.isUpperUnitriangular_def] using hg.mul hh
  inv_mem' := by
    intro g hg
    exact hg.units_inv g

end Ring
end TauCeti
end
