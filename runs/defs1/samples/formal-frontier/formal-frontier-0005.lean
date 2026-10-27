set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace LinearEquiv

universe u

/-- Complete a right-unimodular coefficient row to a self-equivalence of the
finite free module. Following the row-completion statement in Weibel,
*The K-book*, I.1.3, its first output coordinate is the original coefficient
functional, not merely a row equivalent to it. -/
noncomputable def coefficientRowCompletionOfStableRangeCondition
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin (n + 1) → R)
    (ha : Bass.IsRightUnimodular a) {s : ℕ}
    (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n) :
    (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R) := by
  let kerEquiv : LinearMap.ker (Bass.coefficientRowScalarMap R (n + 1) a) ≃ₗ[R]
      (Fin n → R) :=
    (LinearEquiv.ofEq _ _ (Bass.ker_coefficientRowScalarMap_eq R (n + 1) a)).trans
      (Bass.coefficientRowKernelEquivSuccOfStableRangeCondition R n
        (Bass.stableRangeCondition_mono hsn hs) a ha)
  exact (((Bass.kernelProdEquivOfIsRightUnimodular R (n + 1) a ha).symm.trans
    (LinearEquiv.prodComm R _ _)).trans
      ((LinearEquiv.refl R R).prodCongr kerEquiv)).trans
    (Fin.consLinearEquiv R (fun _ : Fin (n + 1) ↦ R))

end LinearEquiv
end
