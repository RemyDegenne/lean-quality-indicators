public section

namespace RootPairing.GeckConstruction

open Function Module.End

open Set hiding diagonal

variable {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] {b : P.Base} [Fintype ι]
  (i j : b.support)

attribute [local simp] Ring.lie_def Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

lemma lie_h_f :
    ⁅h j, f i⁆ = -b.cartanMatrix i j • f i := by
  classical
  suffices ω b * ⁅h j, f i⁆ = ω b * (-b.cartanMatrix i j • f i) by
    replace this := congr(ω b * $this)
    simpa [← mul_assoc, ω_mul_ω] using this
  calc ω b * ⁅h j, f i⁆ = ω b * (h j * f i - f i * h j) := by rw [Ring.lie_def]
                      _ = -(h j * e i - e i * h j) * ω b := ?_
                      _ = -⁅h j, e i⁆ * ω b := by rw [Ring.lie_def]
                      _ = -(b.cartanMatrix i j • e i) * ω b := by rw [lie_h_e]
                      _ = ω b * (-b.cartanMatrix i j • f i) := ?_
  · rw [mul_sub, ← mul_assoc, ← mul_assoc, ω_mul_h, ω_mul_f, mul_assoc, mul_assoc, ω_mul_f, ω_mul_h,
      neg_sub, neg_mul, neg_mul, mul_neg, sub_mul, mul_assoc, mul_assoc]
    abel
  · rw [Matrix.mul_smul, ω_mul_f]
    simp [mul_assoc]

end RootPairing.GeckConstruction
end
