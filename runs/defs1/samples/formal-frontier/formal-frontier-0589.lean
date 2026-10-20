public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped BigOperators ZeroObject

namespace CategoryTheory.AdditiveEuler

universe u v u' v' w

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {Γ : Type w} [AddCommGroup Γ]

variable (μ : C → Γ)

variable (hμ : ∀ S : ShortComplex C, S.ShortExact → μ S.X₂ = μ S.X₁ + μ S.X₃)

include hμ

omit hμ

variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable (ν : D → Γ)

variable (hν : ∀ S : ShortComplex D, S.ShortExact → ν S.X₂ = ν S.X₁ + ν S.X₃)

include hν

omit hν

/-- The native homology comparison for a degreewise mapped chain complex. -/
def map_homology_iso (K : ChainComplex C ℤ) (i : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj K).homology i ≅
      F.obj (K.homology i) := by
  exact (K.sc i).mapHomologyIso F

end CategoryTheory.AdditiveEuler
end
end
