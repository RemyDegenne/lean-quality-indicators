public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul) {inv : ℕ → ℕ}
  {gens : List ℕ}

section Counting

variable (h0 : mul 0 0 = 0)

include h0

theorem kCount_kOrd4 (u : H) : kCount mul (kOrd4 mul N) (Φ.f u) = aOrd4 u := by
  unfold kCount kOrd4 aOrd4
  rw [List.filter_filter]
  have e2 : ∀ x : H, ((mul (Φ.f x) (Φ.f u) == mul (Φ.f u) (Φ.f x)) &&
      (mul (Φ.f x) (Φ.f x) != 0 && mul (mul (Φ.f x) (Φ.f x)) (mul (Φ.f x) (Φ.f x)) == 0)) = true ↔
      x * x ≠ 1 ∧ x * x * (x * x) = 1 ∧ x * u = u * x := by
    intro x
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ← Φ.map_mul, Φ.f_eq_iff,
      f_eq_zero Φ h0]
    tauto
  rw [Nat.card_congr (Equiv.subtypeEquivRight e2).symm]
  exact (Φ.card_eq (fun c => (mul c (Φ.f u) == mul (Φ.f u) c) &&
    (mul c c != 0 && mul (mul c c) (mul c c) == 0))).symm

end Counting
end CFSG.EvenSmallLie.OmegaEight.SpBranch
end
