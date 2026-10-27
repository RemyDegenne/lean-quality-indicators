namespace P2MW.S_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

set_option linter.unusedSectionVars false

noncomputable section

namespace ArchBorelCoord

open AutomorphicForm Topology

variable (K : Type) [Field K] [NumberField K]

scoped instance secondCountable_completion (w : InfinitePlace K) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance secondCountable_Koo : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace K) → w.Completion))

scoped instance secondCountable_units : SecondCountableTopology (InfiniteAdeleRing K)ˣ := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompact_units : LocallyCompactSpace (InfiniteAdeleRing K)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance secondCountable_GL : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompact_GL : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance secondCountable_B : SecondCountableTopology (Bgrp K) := TopologicalSpace.Subtype.secondCountableTopology _

scoped instance locallyCompact_B : LocallyCompactSpace (Bgrp K) := (isClosed_B K).locallyCompactSpace

scoped instance measurableSpace_B : MeasurableSpace (Bgrp K) := borel _

scoped instance borelSpace_B : BorelSpace (Bgrp K) := ⟨rfl⟩

scoped instance measurableSpace_GL : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf _

scoped instance borelSpace_GL : BorelSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf _

def psiG (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ × InfiniteAdeleRing K) : GL (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) p.1 * diagUnits2 p.2.1 1 * unipotentGL2 p.2.2

end ArchBorelCoord
end
end P2MW.S_NumberField_InfiniteAdeleRing_exists_lintegral_borelSubgroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2
