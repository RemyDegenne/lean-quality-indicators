namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace FinitePicard

open MeasureTheory Set intervalIntegral

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem integralNorm_partial {Ω : ℝ → A} {a b t : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (ht : t∈Icc a b) :
    integralNorm Ω a t≤ integralNorm Ω a b :=
  integral_mono_interval le_rfl ht.1 ht.2 (Filter.Eventually.of_forall (fun s => norm_nonneg (Ω s))) hi.norm

end FinitePicard
end DeligneDrinfeld
end
end OAI
