@[expose] public section

universe u v w z

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

omit [Fintype n] in
theorem liftMatrix_eq_one_add_smul (X : Matrix n n R) :
    liftMatrix X = 1 + (DualNumber.eps : DualNumber R) •
      X.map (algebraMap R (DualNumber R)) := by
  ext i j
  · change (1 : Matrix n n R) i j =
        ((1 : Matrix n n (DualNumber R)) i j +
          DualNumber.eps * (algebraMap R (DualNumber R)) (X i j)).fst
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, DualNumber.fst_eps,
      zero_mul, add_zero, Matrix.one_apply, apply_ite, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.fst_zero]
    split_ifs <;> rfl
  · change X i j =
        ((1 : Matrix n n (DualNumber R)) i j +
          DualNumber.eps * (algebraMap R (DualNumber R)) (X i j)).snd
    simp only [TrivSqZeroExt.snd_add, DualNumber.snd_mul, DualNumber.fst_eps,
      DualNumber.snd_eps, zero_mul, one_mul, zero_add,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
      Matrix.one_apply, apply_ite, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_zero]
    simp only [ite_self, zero_add]

end Matrix.DualNumberKernels
end
