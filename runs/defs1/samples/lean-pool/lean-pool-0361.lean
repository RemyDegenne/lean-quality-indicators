@[expose] public section

open Set Function

open CategoryTheory

open scoped Pointwise

noncomputable section

local instance GraphCoveringTheory.Kurosh.kuroshDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

namespace GraphCoveringTheory

namespace Kurosh

open Monoid.CoprodI

/-- Extend the orbit projection to both edge orientations. -/
def rawBassSerreOrbitSymmPrefunctor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Quiver.Symmetrify (RawBassSerreVertex G) ⥤q
      Quiver.Symmetrify (RawBassSerreOrbitVertex G H) :=
  Quiver.Symmetrify.lift (rawBassSerreOrbitPrefunctorToSymm G H)

end Kurosh
end GraphCoveringTheory
end
end
