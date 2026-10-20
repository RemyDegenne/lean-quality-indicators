@[expose] public section

open scoped TrivSqZeroExt

namespace SymmetricAlgebra

universe uR uM uN

variable {R : Type uR} {M : Type uM}

variable [CommRing R] [AddCommGroup M] [Module R M]

@[simp] theorem squareZeroQuotientEquiv_mk_algebraMap (r : R) :
    squareZeroQuotientEquiv (R := R) (M := M)
      (Ideal.Quotient.mk _ (algebraMap R (SymmetricAlgebra R M) r)) =
        TrivSqZeroExt.inl r := by
  change lift (TrivSqZeroExt.inrHom R M)
    (algebraMap R (SymmetricAlgebra R M) r) = TrivSqZeroExt.inl r
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end SymmetricAlgebra
end
