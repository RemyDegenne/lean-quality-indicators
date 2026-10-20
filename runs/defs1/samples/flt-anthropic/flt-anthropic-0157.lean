namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcQuadrupleCor

section Away

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

variable {B : Type} [CommRing B] [Algebra 𝒪 B]

abbrev awayMap (r : B) (M : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K (Localization.Away r) M :=
  AlgebraTensorModule.rTensor 𝒪 (↥M.1) (Algebra.linearMap B (Localization.Away r))

end Away
end P2mKcQuadrupleCor
end
end P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq
