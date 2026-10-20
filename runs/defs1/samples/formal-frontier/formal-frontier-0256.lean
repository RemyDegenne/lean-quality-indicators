set_option autoImplicit false

set_option warningAsError true

public section

open CategoryTheory

noncomputable section

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace OpenSubgroup

/-- Flatten an open subgroup of an open subgroup into the ambient group.
Its underlying subgroup computes as the image of the nested subgroup. -/
@[expose]
def trans (H : OpenSubgroup G) (K : OpenSubgroup H) : OpenSubgroup G where
  toSubgroup := K.toSubgroup.map H.subtype
  isOpen' := by
    change IsOpen (H.subtype '' (K : Set H))
    exact H.isOpen.isOpenMap_subtype_val (K : Set H) K.isOpen

end OpenSubgroup
end
end
