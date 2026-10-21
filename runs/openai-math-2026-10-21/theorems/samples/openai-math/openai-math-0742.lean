namespace OAI

noncomputable section

namespace Tachikawa

open CategoryTheory

open scoped TensorProduct ModuleCat.Algebra

variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

lemma dualRightTensorUnderlying_tmul (φ : dualRightObj (k := k) (R := R))
    (ψ : dualRightObj (k := k) (R := S)) (r : R) (s : S) :
    dualRightTensorUnderlying (φ ⊗ₜ[k] ψ) (r ⊗ₜ[k] s) =
      (show DualBimodule k R from φ) r * (show DualBimodule k S from ψ) s := by
  exact mul_comm _ _

end Tachikawa
end
end OAI
