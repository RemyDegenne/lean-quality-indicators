public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem commutator_le_of_invariant {R : Subgroup G} (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) {r : G}
    (hrR : r ∈ Subgroup.normalizer (R : Set G))
    (hX : ∀ X : Subgroup G, X ≤ R → R ≤ Subgroup.normalizer (X : Set G) →
      r ∈ Subgroup.normalizer (X : Set G) → X ≤ A ∨ X = R) :
    ⁅R, R⁆ ≤ A := by
  rcases hX ⁅R, R⁆ (commutator_self_le R) (fun y hy => mem_normalizer_commutator
    (Subgroup.le_normalizer hy)) (mem_normalizer_commutator hrR) with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsPerfect R := Subgroup.isPerfect_iff.mpr h
    have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
    exact Group.IsPerfect.not_isNilpotent R hR2.isNilpotent

end CFSG.Goldschmidt.Sec8
end
