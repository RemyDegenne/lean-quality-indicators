@[expose] public section

open scoped TrivSqZeroExt

namespace SymmetricAlgebra

universe uR uM uN

variable {R : Type uR} {M : Type uM}

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Evaluation at zero descended to the first-order symmetric-algebra quotient. -/
noncomputable def squareZeroQuotientAugmentation :
    (SymmetricAlgebra R M ⧸ (augmentationIdeal (R := R) (M := M)) ^ 2) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (algebraMapInv (R := R) (M := M)) fun x hx =>
    (mem_augmentationIdeal_iff (R := R) (M := M) x).mp
      ((Ideal.pow_le_self (I := augmentationIdeal (R := R) (M := M))
        (by decide : (2 : ℕ) ≠ 0)) hx)

end SymmetricAlgebra
end
