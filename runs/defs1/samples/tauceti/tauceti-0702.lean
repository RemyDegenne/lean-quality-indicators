public section

open scoped BigOperators

namespace TauCeti.GradedLinearQuiver

universe u v w

variable (R : Type w) [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  {n : ℕ} (X : Fin (n + 1) → C)

/-- Degree-one path operations on suspended Hom modules. An input of suspended degree `d i`
is an original morphism of degree `d i + 1`; the output has original degree `∑ i, d i + 2`. -/
abbrev SuspendedPathOperation := ∀ d : Fin n → ℤ,
  MultilinearMap R (fun i : Fin n ↦ grHom R (X i.rev.castSucc) (X i.rev.succ) (d i + 1))
    (grHom R (X 0) (X (Fin.last n)) (((∑ i, d i) + 1) + 1))

end TauCeti.GradedLinearQuiver
end
