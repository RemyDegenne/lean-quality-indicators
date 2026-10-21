namespace OAI

noncomputable section

open scoped BigOperators

open Finset

open Finset Classical

open Filter

open Finset Classical Filter

open scoped Topology

open MeasureTheory intervalIntegral

open Finset Nat ArithmeticFunction

open scoped ArithmeticFunction.Moebius

open MeasureTheory Filter

open MeasureTheory

open MeasureTheory Set

open Set MeasureTheory Complex

open Set

open Finset Filter

open ArithmeticFunction

open MeasureTheory Finset

open Classical

open Classical Finset

open Classical Finset Real MeasureTheory

open scoped ContDiff

open Filter Finset

namespace OrdinaryCorrelations.ElliottReductions

lemma cesaro_translation_tendsto (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (h : ℕ)
    {z : ℂ} (hz : Tendsto (cesaro a) atTop (nhds z)) :
    Tendsto (cesaro (fun n => a (n + h))) atTop (nhds z) := by
  simpa only [sub_add_cancel, zero_add] using (cesaro_translation_error a ha h).add hz

end OrdinaryCorrelations.ElliottReductions
end
end OAI
