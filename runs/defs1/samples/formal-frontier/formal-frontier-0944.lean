@[expose] public section

open Polynomial

namespace FrobeniusTwistedLine

open scoped TensorProduct

noncomputable section

variable (K : Type*) [Field K]

/-- The universal map from `CoordinateRing` to a pair satisfying its equation. -/
def lift {A : Type*} [CommRing A] [Algebra K A] (p : ℕ) (t : K) (x' y' : A)
    (h : SatisfiesEquation (R := K) (A := A) p t x' y') :
    CoordinateRing K p t →ₐ[K] A :=
  Ideal.Quotient.liftₐ _ (eval K x' y') fun _f hf =>
    RingHom.mem_ker.mp (span_equation_le_ker_eval K p t x' y' h hf)

end
end FrobeniusTwistedLine
end
