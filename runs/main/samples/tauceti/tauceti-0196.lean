public section

namespace TauCeti.DynkinType

open CategoryTheory

open scoped TensorProduct

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {A : Type} [CommRing A] [Algebra 𝔽₂ A]

theorem f4ShortRootWeightTorusConj_quotientLift (s : Fin 4 → Aˣ) (a : Fin 26) :
    (Matrix.lieConj (f4ShortRootWeightTorusGL s : Matrix (Fin 26) (Fin 26) A)
      (Units.invertible (f4ShortRootWeightTorusGL s)))
        (f4ShortRootAdjointMatrixBaseChange (A := A) (f4ShortRootQuotientLift a)) =
      ((torusCharacter s (f4ShortRootQuotientWeight a) : Aˣ) : A) •
        f4ShortRootAdjointMatrixBaseChange (A := A) (f4ShortRootQuotientLift a) := by
  obtain ⟨i | j, rfl⟩ := f4ShortRootWeightIndexEquiv.symm.surjective a
  · simpa only [Matrix.lieConj_apply, Matrix.GeneralLinearGroup.coe_inv,
      f4ShortRootQuotientLift_eq_basis, f4LongRootBasisCoordinate_symm_inl,
      f4ShortRootQuotientWeight_symm_inl,
      f4ModularRootVector_eq_basis] using
        f4ShortRootWeightTorusGL_conj_root s (f4SpecialIsogenyIndexEquiv i)
  · simpa only [Matrix.lieConj_apply, Matrix.GeneralLinearGroup.coe_inv,
      f4ShortRootQuotientLift_eq_basis, f4LongRootBasisCoordinate_symm_inr,
      f4ShortRootQuotientWeight_symm_inr,
      f4ModularSimpleCoroot_eq_basis,
      torusCharacter_zero, Units.val_one, one_smul] using
        f4ShortRootWeightTorusGL_conj_simpleCoroot s
          (f4LongSimpleIndex j)

end
end TauCeti.DynkinType
end
