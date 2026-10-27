set_option warningAsError true

@[expose] public section

universe uN uE uQ uN' uE' uQ'

namespace ContinuousGroupExtension

variable {N : Type uN} {E : Type uE} {Q : Type uQ}
  [Group N] [Group E] [Group Q]
  [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q]

/-- The inclusion, bundled as a continuous homomorphism. -/
def inlContinuous (S : ContinuousGroupExtension N E Q) : N →ₜ* E where
  toMonoidHom := S.inl
  continuous_toFun := S.isSES.isClosedEmbedding.continuous

end ContinuousGroupExtension
end
