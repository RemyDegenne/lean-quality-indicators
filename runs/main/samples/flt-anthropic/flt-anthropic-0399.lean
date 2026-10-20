namespace P2MW.S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural

attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

p2m_open

open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 1600000

set_option Elab.async false

p2m_open

open scoped Classical NumberField NumberField.LevelArith

open scoped TensorProduct Pointwise NumberField.PlaceTransport

private local instance _root_.CycBaseKummerKer.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

private local instance _root_.CycBaseKummerKer.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩

local instance CycBaseKummerKer.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

private local instance _root_.CycBaseKummerKer.normalQbar : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace CycBaseKummerSurj

lemma levelGal_surjective (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
    [Normal ↥K ↥(levelField K L hKL)] : Function.Surjective (levelGal K L hKL) := by
  intro g
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥(levelField K L hKL))
    (E := AlgebraicClosure ℚ) g
  refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm σ, ?_⟩
  show (AlgEquiv.restrictNormalHom _) ((IntermediateField.fixingSubgroupEquiv K)
    ((IntermediateField.fixingSubgroupEquiv K).symm σ)) = g
  rw [MulEquiv.apply_symm_apply]; exact hσ

end CycBaseKummerSurj
end P2MW.S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural
