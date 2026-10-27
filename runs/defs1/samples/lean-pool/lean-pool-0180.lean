@[expose] public section

open Set

namespace QuadraticCarleson.LacunaryVerySmallRange

open QuadraticCarleson.LacunaryMiddleRange

/-- Reindex the integral half-line of admissible modulations by its distance
below the endpoint. -/
noncomputable def verySmallModulationsEquivNat (B c : ℕ) (j : ℤ) :
    verySmallModulations B c j ≃ ℕ where
  toFun m := Int.toNat (verySmallCutoff B c j - (m : ℤ))
  invFun n := ⟨verySmallCutoff B c j - (n : ℤ), by
    rw [mem_verySmallModulations_iff]
    omega⟩
  left_inv m := by
    apply Subtype.ext
    have hm : (m : ℤ) ≤ verySmallCutoff B c j :=
      mem_verySmallModulations_iff.mp m.property
    simp only
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  right_inv n := by
    simp only
    rw [show verySmallCutoff B c j -
        (verySmallCutoff B c j - (n : ℤ)) = (n : ℤ) by ring]
    simp

end QuadraticCarleson.LacunaryVerySmallRange
end
