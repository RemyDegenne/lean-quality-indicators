namespace P2MW.S_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

section S18Body

open scoped S18Inst

scoped instance fact_prime_two_s18 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

scoped instance fact_prime_three_s18 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

scoped instance fact_prime_seven_s18 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

section

section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 1600000

set_option maxRecDepth 8000

namespace FLT

namespace CampGenuineMk

scoped instance gmk6_hil_instOne : One gmk6_hil_SquareClass := ⟨⟨0, 1⟩⟩

scoped instance gmk6_hil_instMul : Mul gmk6_hil_SquareClass :=
  ⟨fun x y => ⟨x.valParity + y.valParity, x.unitSign * y.unitSign⟩⟩

scoped instance gmk6_hil_instInv : Inv gmk6_hil_SquareClass := ⟨fun x => x⟩

scoped instance gmk6_hil_instCommGroup : CommGroup gmk6_hil_SquareClass where
  mul_assoc a b c := gmk6_hil_SquareClass_ext (add_assoc _ _ _) (mul_assoc _ _ _)
  one_mul a := gmk6_hil_SquareClass_ext (zero_add _) (one_mul _)
  mul_one a := gmk6_hil_SquareClass_ext (add_zero _) (mul_one _)
  inv_mul_cancel a := gmk6_hil_SquareClass_ext
    (gmk6_hil_zmod_two_add_self _) (gmk6_hil_units_mul_self _)
  mul_comm a b := gmk6_hil_SquareClass_ext (add_comm _ _) (mul_comm _ _)

theorem gmk6_hil_legendreSign_coe (p : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : (a : ZMod p) ≠ 0) :
    ((gmk6_hil_legendreSign p a : ℤˣ) : ℤ) = legendreSym p a := by
  have _pin := Classical.em True
  rcases legendreSym.eq_one_or_neg_one p ha with h | h
  · unfold gmk6_hil_legendreSign
    rw [if_pos h, h, Units.val_one]
  · unfold gmk6_hil_legendreSign
    rw [if_neg (by rw [h]; norm_num), h]
    simp

end CampGenuineMk
end FLT
end
end
end S18Body
end P2MW.S_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
