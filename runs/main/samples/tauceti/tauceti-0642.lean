public section

open scoped TensorProduct

namespace QuadraticMap

variable {K L E F V : Type*} [CommRing K] [CommRing L] [CommRing E] [CommRing F]
  [Algebra K L] [Algebra K E] [Algebra K F] [Algebra E F] [Algebra L F]
  [IsScalarTower K E F] [IsScalarTower K L F] [Algebra.IsPushout K E L F]
  [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
  [Invertible (2 : K)] [Invertible (2 : L)]

theorem scharlauTransfer_baseChange_comp_cancelBaseChange_symm
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) :
    ((Q.baseChange F).scharlauTransfer
      ((Algebra.IsPushout.out (R := K) (S := E) (R' := L) (S' := F)).toDual s)).comp
        (Algebra.IsPushout.cancelBaseChange K E L F V).symm.toLinearMap =
      (Q.scharlauTransfer s).baseChange E := by
  apply baseChange_ext
  intro v
  simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, scharlauTransfer_apply,
    QuadraticForm.baseChange_tmul, map_one, mul_one, Algebra.smul_def]
  exact IsBaseChange.toDual_comp_apply _ s (Q v)

end QuadraticMap
end
