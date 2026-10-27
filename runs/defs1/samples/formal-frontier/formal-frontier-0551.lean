@[expose] public section

open Polynomial

namespace FrobeniusTwistedLine

open scoped TensorProduct

noncomputable section

variable (K : Type*) [Field K]

/-- Evaluation of `Y` at the dual-number infinitesimal and `X` at zero. -/
def dualNumberEval (L : Type*) [Field L] [Algebra K L] :
    MvPolynomial (Fin 2) K →ₐ[K] DualNumber L :=
  MvPolynomial.aeval fun i => Fin.cases (DualNumber.eps : DualNumber L) (fun _ => 0) i

end
end FrobeniusTwistedLine
end
