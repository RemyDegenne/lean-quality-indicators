set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve.Affine.Point

universe u

variable {F : Type u} [Field F] {W : WeierstrassCurve.Affine F}

variable [DecidableEq F]

variable (P Q : W.Point)

variable {P Q}

variable (W) in

def NetPairingNondegenerate (p : ℕ) : Prop :=
  ∃ P Q : W.Point, p • P = 0 ∧ p • Q = 0 ∧ netPairing p P Q ≠ 1

end WeierstrassCurve.Affine.Point
