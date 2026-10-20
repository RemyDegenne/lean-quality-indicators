public section

namespace TauCeti

open Complex Metric Set

open scoped ComplexConjugate

lemma schwarzPickConjugate_apply_unitDiscMoebiusFormula {f : ℂ → ℂ} {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    schwarzPickConjugate f a ((z - a) / (1 - (starRingEnd ℂ) a * z))
      = (f z - f a) / (1 - (starRingEnd ℂ) (f a) * f z) := by
  have hsource : ((z - a) / (1 - (starRingEnd ℂ) a * z) - -a) /
      (1 - (starRingEnd ℂ) (-a) * ((z - a) / (1 - (starRingEnd ℂ) a * z))) = z :=
    leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha (by simpa [mem_ball_zero_iff] using hz)
  simp only [schwarzPickConjugate, Function.comp_apply, hsource]

end TauCeti
end
