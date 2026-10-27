@[expose] public section

noncomputable section

open scoped unitInterval

namespace AddCircle

/-- The signed `n`-turn loop, obtained by projecting the real segment from `0` to `T * n`.
It is defined also for zero period, when it is constant. -/
def loop (T : ℝ) (n : ℤ) : Path (0 : AddCircle T) 0 :=
  ((Path.segment (0 : ℝ) (T * (n : ℝ))).map (AddCircle.continuous_mk' T)).cast
    rfl (by
      symm
      apply (AddCircle.coe_eq_zero_iff T).mpr
      exact ⟨n, by simp [zsmul_eq_mul, mul_comm]⟩)

end AddCircle
end
end
