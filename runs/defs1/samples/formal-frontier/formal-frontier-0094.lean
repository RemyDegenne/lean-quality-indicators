public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

attribute [instance] AcyclicResolution.hasHomology AcyclicResolution.quasiIso

namespace AcyclicResolution

variable {X A : C} (R : AcyclicResolution X A)

variable {B : C} (R' : AcyclicResolution X B)

variable {R'}

/-- A cochain map induces a map of the canonical cycle short complexes. -/
@[expose] noncomputable def cyclesShortComplexMap
    {X' A' : C} {R' : AcyclicResolution X' A'}
    (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) :
    R.cyclesShortComplex n ⟶ R'.cyclesShortComplex n where
  τ₁ := HomologicalComplex.cyclesMap f n
  τ₂ := f.f n
  τ₃ := HomologicalComplex.cyclesMap f (n + 1)
  comm₁₂ := by simp [cyclesShortComplex]
  comm₂₃ := by
    simpa [cyclesShortComplex] using toCycles_naturality f n

end AcyclicResolution
end CategoryTheory.Abelian.Ext
end
end
