@[expose] public section

noncomputable section

open Complex Filter Function Set TopologicalSpace Topology

open scoped ComplexConjugate

namespace UpperHalfPlane

section IsOpenMap

lemma isOpenMap_im : IsOpenMap im :=
  Complex.isOpenMap_im.comp isOpenEmbedding_coe.isOpenMap

end IsOpenMap
end UpperHalfPlane
end
end
