public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}
  {M : GradedModuleCat.{v} 𝒜}

namespace GradedProjectiveResolution

variable (r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading)

/-- The augmentation of a concrete graded resolution as a morphism of graded modules. -/
abbrev augmentation : r.termObj 0 ⟶ M :=
  GradedModuleCat.ofHom r.π r.isHomogeneous_π

end GradedProjectiveResolution
end TauCeti
end
