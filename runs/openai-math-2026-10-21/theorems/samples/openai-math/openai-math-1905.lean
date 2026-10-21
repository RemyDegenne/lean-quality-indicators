namespace OAI

namespace Laughlin.Charge

open Fock

open scoped BigOperators InnerProductSpace

theorem weighted_car (Q : ℕ) (c : Fin (Q+1) → ℂ) :
    weightedAnnihilate Q c * weightedCreate Q c + weightedCreate Q c * weightedAnnihilate Q c =
      ((∑ i, ‖c i‖^2 : ℝ) : ℂ) • (1 : Module.End ℂ (Space Q)) := by
  have hs : weightedAnnihilate Q c * weightedCreate Q c +
      weightedCreate Q c * weightedAnnihilate Q c =
      ∑ i, ∑ j, (star (c i)*c j) • (annihilate i*create j+create j*annihilate i) := by
    simp only [weightedAnnihilate,weightedCreate,Finset.sum_mul,Finset.mul_sum,
      smul_mul_assoc,mul_smul_comm,Finset.smul_sum,smul_smul,smul_add,Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm]
  rw [hs]
  simp only [mixed_car,ite_smul,one_smul,zero_smul,smul_ite,smul_zero,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true,← Finset.sum_smul,Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change (starRingEnd ℂ) (c i)*c i=((‖c i‖^2 : ℝ) : ℂ)
  rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]

end Laughlin.Charge
end OAI
