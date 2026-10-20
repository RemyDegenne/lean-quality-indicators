@[expose] public section

noncomputable section

open Finset

open Polynomial

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

section aeval

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

section Pi

variable {I : Type*} {A : I → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

variable (x : Π i, A i) (p : R[X])

theorem aeval_pi (x : Π i, A i) : aeval (R := R) x = AlgHom.pi (fun i ↦ aeval (x i)) :=
  (funext fun i ↦ aeval_algHom (Pi.evalAlgHom R A i) x) ▸
    (AlgHom.pi_comp (Pi.evalAlgHom R A) (aeval x))

end Pi
end aeval
end Polynomial
end
end
