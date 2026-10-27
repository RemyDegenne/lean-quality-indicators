set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {R : Type u} [Ring R]

variable {n : Type v} [Fintype n] [DecidableEq n]

/-- An ambient unit congruent to the identity and its inverse lift to mutually
inverse matrices over the ideal's unitization. -/
def liftCongruenceUnit (I : TwoSidedIdeal R)
    (u : congruenceSubgroup (n := n) I) :
    GL n (Unitization ℤ I) where
  val := liftCongruenceMatrix I u
  inv := liftCongruenceMatrix I u⁻¹
  val_inv := by
    apply unitizationMatrix_eq_of_fst_eq_of_idealUnitizationToRing_eq I
    · rw [map_mul, fstHom_map_liftCongruenceMatrix,
        fstHom_map_liftCongruenceMatrix, mul_one, map_one]
    · rw [map_mul, idealUnitizationToRing_map_liftCongruenceMatrix,
        idealUnitizationToRing_map_liftCongruenceMatrix, map_one]
      change (u.1 : Matrix n n R) * u.1.inv = 1
      exact u.1.val_inv
  inv_val := by
    apply unitizationMatrix_eq_of_fst_eq_of_idealUnitizationToRing_eq I
    · rw [map_mul, fstHom_map_liftCongruenceMatrix,
        fstHom_map_liftCongruenceMatrix, mul_one, map_one]
    · rw [map_mul, idealUnitizationToRing_map_liftCongruenceMatrix,
        idealUnitizationToRing_map_liftCongruenceMatrix, map_one]
      change u.1.inv * (u.1 : Matrix n n R) = 1
      exact u.1.inv_val

end Matrix.GeneralLinearGroup
end
