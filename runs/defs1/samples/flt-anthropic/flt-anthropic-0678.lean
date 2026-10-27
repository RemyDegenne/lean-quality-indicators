set_option autoImplicit false

namespace LT.TwistedNorm

section NormEquivVocab

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

def SigmaConjClasses.mk (σ : L ≃ₐ[F] L) (δ : GL (Fin 2) L) : SigmaConjClasses σ :=
  Quotient.mk (sigmaConjSetoid σ) δ

end NormEquivVocab
end LT.TwistedNorm
