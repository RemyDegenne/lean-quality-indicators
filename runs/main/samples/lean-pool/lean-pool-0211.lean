@[expose] public section

open Set Function

open CategoryTheory

open scoped Pointwise

noncomputable section

local instance GraphCoveringTheory.Kurosh.kuroshCoverStarDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

namespace GraphCoveringTheory.Kurosh

open Monoid.CoprodI

theorem Internal.quotientEdgeRawData_cast {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b a' b' : RawBassSerreOrbitVertex G H}
    (ha : a = a') (hb : b = b')
    (e : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b) :
    quotientEdgeRawData G H (Quiver.Hom.cast ha hb e) =
      quotientEdgeRawData G H e := by
  cases ha
  cases hb
  rfl

end GraphCoveringTheory.Kurosh
end
end
