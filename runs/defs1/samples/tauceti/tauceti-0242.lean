open Equiv MulAction

public section

namespace TauCeti

namespace PassportSpec

variable {n : ℕ}

/-- A passport is admissible when its degree is nonzero, its reference subgroup is transitive,
and its three multisets are partitions of the degree into positive parts. -/
def IsAdmissible (P : PassportSpec n) : Prop :=
  n ≠ 0 ∧
    IsPretransitive P.G (Fin n) ∧
    (P.lam0.sum = n ∧ ∀ i ∈ P.lam0, 0 < i) ∧
    (P.lam1.sum = n ∧ ∀ i ∈ P.lam1, 0 < i) ∧
    (P.laminf.sum = n ∧ ∀ i ∈ P.laminf, 0 < i)

end PassportSpec
end TauCeti
end
