set_option warningAsError true

@[expose] public section

noncomputable section

universe uN uE uQ uH

namespace ContinuousGroupExtension

variable {N : Type uN} {E : Type uE} {Q : Type uQ}
  [Group N] [Group E] [Group Q]
  [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q]

/-- The quotient-group action on the topological abelianization of the kernel. -/
noncomputable def quotientConjActTopologicalAbelianization
    (S : ContinuousGroupExtension N E Q) :
    Q →* MulAut (TopologicalAbelianization N) :=
  (QuotientGroup.lift S.rightHom.ker S.conjActTopologicalAbelianization
    S.ker_rightHom_le_ker_conjActTopologicalAbelianization).comp
      S.toGroupExtension.quotientKerRightHomEquivRight.symm.toMonoidHom

end ContinuousGroupExtension
end
end
