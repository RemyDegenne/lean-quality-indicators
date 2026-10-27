set_option autoImplicit false

namespace AlgebraicCurve

open IsLocalRing

open scoped Pointwise

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def ComponentChart.HasAffinoidLifting (C : ComponentChart A F Fbar) (N : Finset (Place (ResidueField A) Fbar)) : Prop :=
  (∀ f : F, C.tubeBounded f → f ∈ C.integers) ∧
  (∀ g : Fbar, (∀ Q : Place (ResidueField A) Fbar, Q ∉ N → g ∈ Q.toValuationSubring) →
    ∃ (f : F) (hf : f ∈ C.integers), C.tubeBounded f ∧ C.residue ⟨f, hf⟩ = g) ∧
  ∀ h : F, h ∈ C.integers → ∃ (r s : F) (hs : s ∈ C.integers),
    C.tubeBounded r ∧ C.tubeBounded s ∧ C.residue ⟨s, hs⟩ ≠ 0 ∧ h * s = r

end AlgebraicCurve
