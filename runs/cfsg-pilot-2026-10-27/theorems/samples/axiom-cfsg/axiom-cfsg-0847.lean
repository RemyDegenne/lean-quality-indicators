namespace CFSG.FeitThompson

public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

open Subgroup MulAction

variable {N : Type*} [Group N]

theorem fixedPoints_range_eq_top_of_coprime_of_isNilpotent [Finite N] [Group.IsNilpotent N]
    {A : Type*} [Group A] [Finite A] (φ : A →* MulAut N)
    (hcop : (Nat.card A).Coprime (Nat.card N))
    (hself : centralizer (FixedPoints.subgroup φ.range N : Set N) ≤
      FixedPoints.subgroup φ.range N) :
    FixedPoints.subgroup φ.range N = ⊤ := by
  refine fixedPoints_subgroup_eq_top_of_isNilpotent_of_centralizer_le φ.range
    (n := Nat.card A) hcop ?_ hself
  rintro b ⟨a, rfl⟩
  rw [← map_pow, pow_card_eq_one', map_one]

end
end CFSG.FeitThompson
