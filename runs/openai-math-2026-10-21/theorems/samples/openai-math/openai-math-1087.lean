namespace OAI

noncomputable section

open scoped BigOperators

open MeasureTheory intervalIntegral

open Finset

open Finset Nat ArithmeticFunction

open scoped ArithmeticFunction.Moebius

open Filter

open MeasureTheory Filter

open MeasureTheory

namespace OrdinaryLogDerivative

open LSeries MeasureTheory

lemma horizontal_hasDerivAt {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hm : Complete f) (s : ℂ) {x : ℝ} (hs : 1 < (s+x).re) :
    HasDerivAt (fun x : ℝ => LSeries f (s+x))
      (-(LSeries (mangoldtTwist f) (s+x)*LSeries f (s+x))) x := by
  have hab : LSeries.abscissaOfAbsConv f < ((s+x).re: EReal) :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => hf n⟩)
      (by exact_mod_cast hs)
  have hd := (LSeries_hasDerivAt hab).differentiableAt.hasDerivAt
  rw [LSeries_derivative_product hf hm hs] at hd
  have hp := (hasDerivAt_id (x:ℂ)).const_add s
  simpa only [Function.comp_def,id_eq,mul_one] using (hd.comp (x:ℂ) hp).comp_ofReal

end OrdinaryLogDerivative
end
end OAI
