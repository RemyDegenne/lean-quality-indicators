public section

open CategoryTheory Limits ComposableArrows HomotopyCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

section SpectralObject

variable {ι : Type*} [Category* ι] (F : ι ⥤ CochainComplex C ℤ)

/-- The objects `H^n(f)` of the spectral object of `F` are the cohomology of the mapping cones of
the maps `F.map f`. -/
noncomputable def spectralObjectHIso {i j : ι} (f : i ⟶ j) (n : ℤ) :
    ((spectralObject F).H n).obj (mk₁ f) ≅ (mappingCone (F.map f)).homology n :=
  (homologyFunctorFactors C (ComplexShape.up ℤ) n).app (mappingCone (F.map f))

end SpectralObject
end CochainComplex
end
