namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators Topology

open scoped BigOperators Topology InnerProductSpace

open scoped BigOperators Topology

namespace CriticalSK

section

open Set Filter MeasureTheory

variable {n : ℕ} (W : Disorder n)

lemma centeredPointDensity_mean (x : Spin n) : mean W (centeredPointDensity W x)=0 := by
  change mean W (fun y => (if y=x then (gibbs W x)⁻¹ else 0)-1)=0
  rw [mean_sub,mean_const]
  unfold mean
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [mul_inv_cancel₀ (gibbs_pos W x).ne',sub_self]

end
end CriticalSK
end
end OAI
