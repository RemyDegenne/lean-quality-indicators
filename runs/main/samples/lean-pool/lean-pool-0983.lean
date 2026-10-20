@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped BigOperators

section IndexedWronskian

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

theorem indexedAuxiliaryWronskian_det_eq_derivationWronskian_det
    (D : Derivation C L L) (h k : ℕ)
    (f : Sum (Fin k) (Fin (k + 1) × Fin h) → L) :
    (indexedDedekindLocalWronskian D
      (auxiliaryFamilyDerivativeOrder h k) f).det =
      (BGS.Algebra.derivationWronskian D
        (fun j : Fin (h * k + h + k) =>
          f ((auxiliaryFamilyIndexEquiv h k).symm j))).det := by
  let e := auxiliaryFamilyIndexEquiv h k
  let g : Fin (h * k + h + k) → L := fun j => f (e.symm j)
  have hmatrix :
      indexedDedekindLocalWronskian D
          (auxiliaryFamilyDerivativeOrder h k) f =
        Matrix.reindex e.symm e.symm
          (BGS.Algebra.derivationWronskian D g) := by
    ext i j
    simp only [indexedDedekindLocalWronskian, auxiliaryFamilyDerivativeOrder, Matrix.reindex_apply,
      Matrix.submatrix, Algebra.derivationWronskian, Equiv.symm_symm, Equiv.symm_apply_apply,
      Matrix.of_apply, e, g]
    exact (Module.End.pow_apply D.toLinearMap _ (f j)).symm
  rw [hmatrix, Matrix.det_reindex_self]

end IndexedWronskian
end
end BGS.CorvajaZannier
end
