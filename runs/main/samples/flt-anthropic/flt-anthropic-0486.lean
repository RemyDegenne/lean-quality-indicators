namespace P2MW.S_ModularCurve_moduliPlace_restrictAlong_inclusion

set_option autoImplicit false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

noncomputable section

namespace P2MKcDegC6

universe u v

section CycSub

variable {A : Type*} [AddCommGroup A] {N : ℕ}

theorem addOrderOf_div_nsmul {M : ℕ} (hMN : M ∣ N) (hN : N ≠ 0) {g : A} (hg : addOrderOf g = N) :
    addOrderOf ((N / M) • g) = M := by
  have hM0 : 0 < M := Nat.pos_of_dvd_of_pos hMN (Nat.pos_of_ne_zero hN)
  have hq : 0 < N / M := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hMN) hM0
  rw [addOrderOf_nsmul' _ hq.ne', hg, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hMN),
    Nat.div_div_self hMN hN]

end CycSub
end P2MKcDegC6
end
end P2MW.S_ModularCurve_moduliPlace_restrictAlong_inclusion
