public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open SemidirectProduct

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v w

variable {A V : Type*} [Group A] [Group V] [Finite A] [Finite V] [Group.IsSolvable A]
  [Group.IsSolvable V] {ι : Type*} [Fintype ι]

theorem prod_natCard_fixedPoints_comp_subtype_pow_eq (ρ : A →* MulAut V)
    (hcop : (Nat.card A).Coprime (Nat.card V)) (B : ι → Subgroup A)
    [∀ i, DecidablePred (· ∈ B i)] (m n : ι → ℕ)
    (hmn : ∀ a : A, ∑ i with a ∈ B i, m i = ∑ i with a ∈ B i, n i) :
    ∏ i, Nat.card (FixedPoints.subgroup (ρ.comp (B i).subtype).range V) ^ (m i * Nat.card (B i))
      = ∏ i, Nat.card (FixedPoints.subgroup (ρ.comp (B i).subtype).range V)
          ^ (n i * Nat.card (B i)) :=
  prod_natCard_fixedPoints_comp_subtype_pow_eq_of_natCard_le B m n hmn (Nat.card V) ρ le_rfl hcop

end CFSG.FeitThompson
end
