namespace P2MW.S_AutomorphicForm_archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj

set_option autoImplicit false

open NumberField

open scoped TensorProduct TensorProduct.RightActions NumberField.LiesOver

noncomputable section

namespace TwPT

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (g : L ≃ₐ[K] L) (w' : NumberField.InfinitePlace L)

theorem algebraMap_withAbs_apply (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K) [w.1.LiesOver v.1]
    (x : WithAbs v.1) :
    algebraMap (WithAbs v.1) (WithAbs w.1) x = (WithAbs.equiv w.1).symm (algebraMap K L (WithAbs.equiv v.1 x)) := rfl

end TwPT
end
end P2MW.S_AutomorphicForm_archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj
