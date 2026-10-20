set_option warningAsError true

@[expose] public section

universe uN uE uQ uN' uE' uQ'

namespace ContinuousGroupExtension

variable {N : Type uN} {E : Type uE} {Q : Type uQ}
  [Group N] [Group E] [Group Q]
  [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q]

/-- Construct a continuous group extension from an abstract extension and the
strong topological short-exactness witness. -/
def mk' (S : GroupExtension N E Q)
    (hS : TopologicalGroup.IsSES S.inl S.rightHom) :
    ContinuousGroupExtension N E Q where
  toGroupExtension := S
  isSES := hS

end ContinuousGroupExtension
end
