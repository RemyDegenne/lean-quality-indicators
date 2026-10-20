set_option warningAsError true

@[expose] public section

universe uN uE uQ uN' uE' uQ'

namespace ContinuousGroupExtension

variable {N : Type uN} {E : Type uE} {Q : Type uQ}
  [Group N] [Group E] [Group Q]
  [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q]

/-- The projection, bundled as a continuous homomorphism. -/
def rightHomContinuous (S : ContinuousGroupExtension N E Q) : E →ₜ* Q where
  toMonoidHom := S.rightHom
  continuous_toFun := S.isSES.isOpenQuotientMap.continuous

end ContinuousGroupExtension
end
