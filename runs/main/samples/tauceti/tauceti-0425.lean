public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w w₁

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M]

variable (b : (IsKilling.rootSystem H).Base)

variable {b}

theorem isHighestWeightVector_iff {lam : Dual K H} {v : M} :
    IsHighestWeightVector b lam v ↔
      v ≠ 0 ∧ (∀ x : H, ⁅(x : L), v⁆ = lam x • v) ∧
        ∀ x ∈ positiveNilradical H b, ⁅x, v⁆ = 0 :=
  Iff.rfl

end TauCeti
end
