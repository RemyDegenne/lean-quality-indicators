@[expose] public section

noncomputable section

open scoped Nat Real Interval

open Complex MeasureTheory Set intervalIntegral

local notation "𝕌" => UnitAddCircle

section BernoulliFunProps

section Evaluation

theorem bernoulliFun_eval_zero (k : ℕ) : bernoulliFun k 0 = bernoulli k := by
  rw [bernoulliFun, Polynomial.eval_zero_map, Polynomial.bernoulli_eval_zero, eq_ratCast]

end Evaluation
end BernoulliFunProps
end
end
