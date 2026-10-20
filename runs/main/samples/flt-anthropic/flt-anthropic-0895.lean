namespace P2MW.S_HeckeEis_exists_filtration_binaryForm_subquotient_le_sub_one

set_option autoImplicit false

namespace ATHRFilt

open MvPolynomial HeckeEis Finset

section Eval

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p]

theorem pow_add_mul_sub_one {x : K} (hx : x ^ p = x) {j : ℕ} (hj : 1 ≤ j) (q : ℕ) :
    x ^ (j + q * (p - 1)) = x ^ j := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.out.one_le
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    calc x ^ (j' + 1 + (q + 1) * (p - 1))
        = x ^ (j' + 1 + q * (p - 1)) * x ^ (p - 1) := by rw [← pow_add]; congr 1; ring
      _ = x ^ j' * (x ^ (p - 1) * x) := by rw [ih]; ring
      _ = x ^ (j' + 1) := by rw [← pow_succ, hp1, hx, pow_succ]

end Eval
end ATHRFilt
end P2MW.S_HeckeEis_exists_filtration_binaryForm_subquotient_le_sub_one
