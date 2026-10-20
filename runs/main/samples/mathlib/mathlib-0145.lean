@[expose] public section

namespace List.Nat

theorem mem_antidiagonalTuple {n : ℕ} {k : ℕ} {x : Fin k → ℕ} :
    x ∈ antidiagonalTuple k n ↔ ∑ i, x i = n := by
  induction x using Fin.consInduction generalizing n with
  | elim0 =>
    cases n
    · decide
    · simp
  | cons x₀ x ih =>
    simp_rw [Fin.sum_cons, antidiagonalTuple, List.mem_flatMap, List.mem_map,
      List.Nat.mem_antidiagonal, Fin.cons_inj, exists_eq_right_right, ih,
      @eq_comm _ _ (Prod.snd _), and_comm (a := Prod.snd _ = _),
      ← Prod.mk_inj (a₁ := Prod.fst _), exists_eq_right]

end List.Nat
end
