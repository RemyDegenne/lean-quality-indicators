@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x

namespace GeneralLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type v) [Fintype n] [DecidableEq n]

@[simp] theorem quotientEquiv_symm_entry (i j : n) :
    (quotientEquiv K n).symm (AdjoinRoot.of _ (MvPolynomial.X (i, j))) =
      matrix K n i j := by
  rw [← quotientEquiv_matrix K n i j, AlgEquiv.symm_apply_apply]

end GeneralLinearCoordinateRing
end
end
