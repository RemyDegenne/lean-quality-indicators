set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve.RegularProlongation

open IsLocalRing

open scoped Pointwise

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

section ResAut

variable (R : RegularProlongation A F Fbar) (τ : F ≃ₐ[L] F) (hτ : ∀ f : F, τ f ∈ R.integers ↔ f ∈ R.integers)

def residueEquiv : (R.integers ⧸ RingHom.ker R.residue) ≃+* Fbar :=
  RingHom.quotientKerEquivOfSurjective R.residue_surjective

end ResAut
end AlgebraicCurve.RegularProlongation
end
