@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {E : Type*} [Group E]

theorem orderOf_eq_two' {X : Type*} [Group X] {g : X} (h2 : g * g = 1) (h1 : g ≠ 1) :
    orderOf g = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two, h2]) h1

end CFSG.ComponentClassification.GrSLit.L34Facts
end
