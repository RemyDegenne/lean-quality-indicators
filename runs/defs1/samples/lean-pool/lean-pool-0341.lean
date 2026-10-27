@[expose] public noncomputable section

open Filter

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Open-neighborhood local quadratic bump data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeLocalQuadraticOpenBump
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticOpenBumpAt C boundary F g B x J

end ViscositySolns
end
