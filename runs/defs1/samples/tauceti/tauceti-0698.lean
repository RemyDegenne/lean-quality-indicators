public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty ZeroObject

universe uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A)

variable {𝒜}

attribute [instance] gradedSMul

/-- The induced graded exact structure on finite graded modules: the full-subcategory exact
structure of the graded abelian exact structure for the grading shift. Its Laurent Grothendieck
group is the graded Grothendieck group of finite graded modules, which is the usual
`G₀^gr(mod A)` when `A` is noetherian. -/
@[expose] noncomputable def gradedFiniteModulesExactStructure (𝒜 : ℤ → Submodule k A) :
    GradedExactStructure (gradedFiniteModules 𝒜).FullSubcategory :=
  (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).fullSubcategory _
    isExtensionClosed_gradedFiniteModules_gradedAbelian
      gradedFiniteModules_gradedAbelian_shift

end TauCeti
end
end
