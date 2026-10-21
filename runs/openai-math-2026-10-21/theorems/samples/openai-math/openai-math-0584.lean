namespace OAI

noncomputable section

open Set MeasureTheory

open scoped BigOperators Interval

namespace TriangularCovering.AngularSampling

lemma sample_term_remainder {ε a b q : ℝ} (he : |ε| ≤ 1)
    (hq : |q| ≤ 1) (hab : a ≤ b) :
    |sampleTerm ε a b q - (b-a)*(1/4 + ε^2*areaDensity q)| ≤
      (b-a)*5*ε^4 := by
  have hqB := node_bounds hq
  have hd := d_bounds hq
  have hM0 : 0 ≤ η+d q := by unfold η; linarith only [hd.1]
  have hM1 : η+d q ≤ 1 := by unfold η; linarith only [hd.2]
  have he2 : ε^2 ≤ 1 := by nlinarith only [(abs_le.mp he).1,(abs_le.mp he).2]
  have h := bounded_product_remainder (sq_nonneg ε) he2 hM0 hM1 hqB.2.2.2.1 hqB.2.2.2.2
  have hid : sampleTerm ε a b q - (b-a)*(1/4+ε^2*areaDensity q) =
      (b-a)*((1/2+ε^2*(η+d q))^2 / Real.sqrt (1+ε^2*nodeSpeed q) -
        (1/4+ε^2*((η+d q)-nodeSpeed q/8))) := by
    unfold sampleTerm areaDensity nodeSpeed nodeAlpha nodeBeta; ring
  rw [hid,abs_mul,abs_of_nonneg (sub_nonneg.mpr hab)]
  calc
    _ ≤ (b-a)*(5*(ε^2)^2) := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hab)
    _ = (b-a)*5*ε^4 := by ring

end TriangularCovering.AngularSampling
end
end OAI
