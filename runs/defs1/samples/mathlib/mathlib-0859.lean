@[expose] public section

open Ideal Quotient

variable {R S : Type*} [NonAssocSemiring R] [CommRing S] (I : Ideal S)

namespace IsAdicComplete

open AdicCompletion

section

variable [IsAdicComplete I S] (f : (n : ℕ) → R →+* S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n), (factorPow I hle).comp (f n) = f m)

section

variable {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal S)
  [IsAdicComplete I S] [CommRing A] [Algebra R A]

/-- `AlgHom` version of `IsAdicCompletion.liftRingHom`. -/
noncomputable
def liftAlgHom (f : (n : ℕ) → A →ₐ[R] S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m) :
    A →ₐ[R] S :=
  ((ofAlgEquiv I).symm.toAlgHom.restrictScalars R).comp (AdicCompletion.liftAlgHom I f hf)

end
end
end IsAdicComplete
end
