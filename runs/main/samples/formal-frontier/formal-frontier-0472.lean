@[expose] public section

open scoped TensorProduct

universe uR uC uM uN uD uM' uN'

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

theorem tensorProdLeft_symm_comp_inr
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R) :
  (tensorProdLeft R C D M).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr R (tensorLeftObj R C M) (tensorLeftObj R D M)) =
      tensorMapCLM R (C := D) (D := ModuleCat.of R (C × D))
        (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M) := by
  rw [tensorProdLeft_symm_toContinuousLinearMap,
    ContinuousLinearMap.comp_fst_add_comp_snd, ContinuousLinearMap.coprod_comp_inr]

end TopModuleCat
end
