namespace P2MW.S_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_and_weighted_eq_mul_prod_norm_pow_mul_integral_integral_of_scalar_mul_diagUnits2

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option synthInstance.maxSize 8192

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

namespace HCDescentArch

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

scoped instance measurableSpace_GL : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf _

scoped instance borelSpace_GL : BorelSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf _

scoped instance (priority := high) measurableSpace_Kc : MeasurableSpace (Kc K) := borel _

scoped instance borelSpace_Kc : BorelSpace (Kc K) := ⟨rfl⟩

scoped instance secondCountable_Kc : SecondCountableTopology (Kc K) := TopologicalSpace.Subtype.secondCountableTopology _

scoped instance compactSpace_Kc : CompactSpace (Kc K) :=
  isCompact_iff_compactSpace.mp
    (NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup K).2

theorem unipotent_conj (u z : (InfiniteAdeleRing K)ˣ) (x : InfiniteAdeleRing K) :
    (unipotentGL2 x : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) *
        unipotentGL2 x =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 *
        unipotentGL2 (((1 : InfiniteAdeleRing K) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) * x) := by
  rw [unipotentGL2_inv, scalar_mul_diagUnits2]
  apply Units.ext
  simp only [Units.val_mul, unipotentGL2_coe, diagUnits2_val']
  have hu : (u : InfiniteAdeleRing K) * ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1 := Units.mul_inv u
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination ((z : InfiniteAdeleRing K) * x) * hu

end HCDescentArch
end
end P2MW.S_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_and_weighted_eq_mul_prod_norm_pow_mul_integral_integral_of_scalar_mul_diagUnits2
