public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped BigOperators ZeroObject

namespace CategoryTheory.AdditiveEuler

universe u v w

variable {Γ : Type w} [AddCommGroup Γ]

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (μ : C → Γ)

variable (hμ : ∀ S : ShortComplex C, S.ShortExact → μ S.X₂ = μ S.X₁ + μ S.X₃)

include hμ

omit hμ

/-- Native homology shift comparison, with target degree `i + n`. -/
def cochain_shift_homology_iso (K : CochainComplex C ℤ) (n i : ℤ) :
    (K⟦n⟧).homology i ≅ K.homology (i + n) :=
  (CochainComplex.ShiftSequence.shiftIso C n i (i + n) (by omega)).app K

end CategoryTheory.AdditiveEuler
end
end
