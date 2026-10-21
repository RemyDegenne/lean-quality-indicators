namespace OAI

open MeasureTheory Set

open scoped ENNReal BigOperators

open Set Filter

open scoped Topology

namespace StandardMapEntropy

lemma transferStep_cone (v : ℝ) (B : ℝ) (hB : 2 ≤ B) (hv : B ≤ |v|) (z : ℂ)
    (hz : |z.im| ≤ |z.re|) :
    (B-1)*|z.re| ≤ |(transferStep v z).re| ∧ |(transferStep v z).im| ≤ |(transferStep v z).re| := by
  have htri := abs_sub_abs_le_abs_sub (v*z.re) z.im
  rw [abs_mul] at htri
  have hm := mul_le_mul_of_nonneg_right hv (abs_nonneg z.re)
  simp only [transferStep_re,transferStep_im]
  constructor <;> nlinarith [abs_nonneg z.re]

end StandardMapEntropy
end OAI
