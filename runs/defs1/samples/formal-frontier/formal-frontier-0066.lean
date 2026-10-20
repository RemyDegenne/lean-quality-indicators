set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

/-- The abstract degree-one cocycles of the homogeneous complex, identified
with the explicit kernel of its degree-one differential. -/
noncomputable abbrev cocyclesOneIso : cocycles X 1 ≅
    ↧((TopRep.homogeneousCochains X).d 1 2).hom.ker :=
  Limits.KernelFork.mapIsoOfIsLimit
    ((TopRep.homogeneousCochains X).cyclesIsKernel 1 2 (by simp))
    (TopModuleCat.isLimitKer _) (Iso.refl _)

end ContinuousCohomology
end
