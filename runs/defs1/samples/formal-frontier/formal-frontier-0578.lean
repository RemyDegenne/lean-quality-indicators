public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Kernels of the norm, functorially in the representation. -/
@[expose]
noncomputable def normKernelFunctor : Rep R G ⥤ ModuleCat R :=
  normArrowFunctor ⋙ Limits.ker (ModuleCat R)

end FiniteGroupTateCohomology
end
