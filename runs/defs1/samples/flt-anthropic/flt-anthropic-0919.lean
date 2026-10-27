namespace P2MW.S_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank

set_option synthInstance.maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

attribute [-instance] Quotient.instLE_mathlib

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_GaloisTensorNorm

set_option autoImplicit false

open scoped TensorProduct

namespace M4aHerbrand

namespace GaloisTensor

p2m_open

p2m_reactivate

section SplitOver

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

variable (C : Type*) [CommRing C] [Algebra K C] [Algebra L C] [IsScalarTower K L C]

open Classical in

noncomputable def splitEquivOver : C ⊗[K] L ≃ₐ[C] ((L ≃ₐ[K] L) → C) :=
  (Algebra.TensorProduct.cancelBaseChange K L C C L).symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[C] C) (splitEquiv K L)).trans <|
      (Algebra.TensorProduct.piRight L C C (fun _ : L ≃ₐ[K] L => L)).trans <|
        AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.rid L C C

end SplitOver
end GaloisTensor
end M4aHerbrand
end Fold_GaloisTensorNorm
end P2MW.S_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank
