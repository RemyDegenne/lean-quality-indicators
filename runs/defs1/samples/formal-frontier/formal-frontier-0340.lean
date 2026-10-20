set_option warningAsError true

@[expose] public section

namespace Unitization

universe u v

variable (R : Type u) (A : Type v)

variable [CommRing R] [Ring A] [Algebra R A]

/-- The canonical ring equivalence from the unitization of a unital algebra to
the product of its scalar ring and the algebra itself.  It sends `(r, a)` to
`(r, algebraMap R A r + a)`. -/
def ringEquivProd : Unitization R A ≃+* R × A where
  toFun x := (x.fst, algebraMap R A x.fst + x.snd)
  invFun x := Unitization.mk (x.1, x.2 - algebraMap R A x.1)
  left_inv x := by
    apply Unitization.ext
    · rfl
    · simp
  right_inv x := by
    apply Prod.ext
    · rfl
    · simp
  map_add' x y := by
    apply Prod.ext
    · rfl
    · change algebraMap R A (x.fst + y.fst) + (x.snd + y.snd) =
        (algebraMap R A x.fst + x.snd) +
          (algebraMap R A y.fst + y.snd)
      rw [map_add]
      abel
  map_mul' x y := by
    apply Prod.ext
    · exact Unitization.fst_mul x y
    · change algebraMap R A (x.fst * y.fst) +
          (x.fst • y.snd + y.fst • x.snd + x.snd * y.snd) =
        (algebraMap R A x.fst + x.snd) *
          (algebraMap R A y.fst + y.snd)
      simp only [map_mul, Algebra.smul_def]
      rw [Algebra.commutes y.fst x.snd]
      noncomm_ring

end Unitization
end
