public section

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

@[simp] theorem superdiagonalQuotientEquiv_mk (r : ℕ) (hr : 1 ≤ r)
    (x : superdiagonalSubgroup n R r) (ij : superdiagonalIndex n r) :
    Multiplicative.toAdd
        (superdiagonalQuotientEquiv n R r hr
          (x : superdiagonalSubgroup n R r ⧸
            (superdiagonalSubgroup n R (r + 1)).subgroupOf
              (superdiagonalSubgroup n R r))) ij =
      (x.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2 := by
  simp [superdiagonalQuotientEquiv]

end Matrix.UnitriangularGroup
end
