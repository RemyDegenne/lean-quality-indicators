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

/-- Map a tree path to the symmetrified quotient graph without bundled tree vertices. -/
def rawTreeInclusionMapPathAsRaw {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H)}
    (p : @Quiver.Path (WideSubquiver.toType
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (rawBassSerreOrbitTree G H))
      (WideSubquiver.quiver (rawBassSerreOrbitTree G H)) a b) :
    @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (show RawBassSerreOrbitVertex G H from a)
      (show RawBassSerreOrbitVertex G H from b) := by
  exact (rawTreeInclusion G H).mapPath p

end Kurosh
end GraphCoveringTheory
end
end
