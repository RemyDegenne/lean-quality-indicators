@[expose] public section

namespace RS

universe u u' v

attribute [instance] SuperCommAlgebra.evenAddCommGroup
  SuperCommAlgebra.evenModule SuperCommAlgebra.oddAddCommGroup
  SuperCommAlgebra.oddModule

attribute [instance] SuperMod.evenAddCommGroup SuperMod.evenModule
  SuperMod.oddAddCommGroup SuperMod.oddModule

namespace SuperMod

open CategoryTheory

/-- A morphism of super modules: a pair of ℂ-linear maps
preserving the grading. -/
@[ext]
structure Hom (V W : SuperMod.{u}) where
  /-- The even component of the morphism. -/
  evenMap : V.even →ₗ[ℂ] W.even
  /-- The odd component of the morphism. -/
  oddMap : V.odd →ₗ[ℂ] W.odd

end SuperMod
end RS
end
