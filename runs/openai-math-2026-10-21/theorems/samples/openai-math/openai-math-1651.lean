namespace OAI

namespace PolynomialVacuumAlgebra

open Classical

theorem braidTrain_spectator_swap (c : ℂ) (X : ℕ → ℂ) (k d m : ℕ) :
    siteR (k+d) (X (k+d)) (X (k+d+1)) * braidTrain c X k (d+(m+2)) =
      braidTrain c (swapSite (k+d) X) k (d+(m+2)) *
        siteR (k+d+1) (X (k+d)) (X (k+d+1)) := by
  induction d generalizing k with
  | zero =>
    simp only [Nat.add_zero,Nat.zero_add]
    have hc := braidTrain_far_left c X k (k+1+1) m (by omega) (X k) (X (k+1))
    have ht : braidTrain c (swapSite k X) (k+1+1) m=braidTrain c X (k+1+1) m := by
      apply braidTrain_congr
      intro i hi hi'
      exact swapSite_other (by omega) (by omega) X
    simp only [braidTrain,swapSite_left,swapSite_right,ht]
    calc
      siteR k (X k) (X (k+1)) *
        (braidTrain c X (k+1+1) m * siteR (k+1) c (X (k+1)) * siteR k c (X k)) =
        braidTrain c X (k+1+1) m *
          (siteR k (X k) (X (k+1))*siteR (k+1) c (X (k+1))*siteR k c (X k)) := by
            rw [← mul_assoc,← mul_assoc,hc]; simp only [mul_assoc]
      _ = _ := by rw [siteR_yang_baxter]; simp only [mul_assoc]
  | succ d ih =>
    have hp : k+(d+1)=(k+1)+d := by omega
    have hl : (d+1)+(m+2)=(d+(m+2))+1 := by omega
    have ho : swapSite (k+(d+1)) X k=X k := swapSite_other (by omega) (by omega) X
    rw [hl,braidTrain,braidTrain]
    simp only [ho]
    calc
      siteR (k+(d+1)) (X (k+(d+1))) (X (k+(d+1)+1)) *
          (braidTrain c X (k+1) (d+(m+2))*siteR k c (X k)) =
        (braidTrain c (swapSite (k+(d+1)) X) (k+1) (d+(m+2))*
          siteR (k+(d+1)+1) (X (k+(d+1))) (X (k+(d+1)+1)))*siteR k c (X k) := by
            rw [← mul_assoc,hp,ih (k+1)]
      _ = _ := by
        rw [mul_assoc,siteR_far_comm (Or.inr (by omega)),← mul_assoc]

end PolynomialVacuumAlgebra
end OAI
