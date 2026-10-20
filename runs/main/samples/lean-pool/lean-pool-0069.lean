@[expose] public section

open Finset UniqueFactorizationMonoid

section

open Asymptotics Filter

lemma tripleAt_strictMono : StrictMono tripleAt := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [tripleAt, Prod.mk_lt_mk, lt_self_iff_false, Prod.mk_le_mk, tsub_le_iff_right,
    false_and, le_refl, true_and, false_or]
  right
  constructor
  · rw [mul_add_one, pow_add]
    omega
  · gcongr
    · simp
    · simp

end
end
