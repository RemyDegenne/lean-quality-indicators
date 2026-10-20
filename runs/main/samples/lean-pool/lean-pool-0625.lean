@[expose] public noncomputable section

open Filter MeasureTheory Metric Set

open scoped Topology

namespace ViscositySolns

variable {n : Nat}

theorem integral_coordSecondDifference_mul {f g : Point n → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (h : ℝ) :
    ∫ x, coordSecondDifference f h x * g x = ∫ x, f x * coordSecondDifference g h x := by
  have hcsd : ∀ v : Point n, Continuous (centralSecondDifference f v) := fun v =>
    ((hf.comp (continuous_id.add continuous_const)).add
      (hf.comp (continuous_id.sub continuous_const))).sub (continuous_const.mul hf)
  have hintL : ∀ i : Fin n,
      Integrable (fun x => centralSecondDifference f (h • Pi.single i 1) x * g x) :=
    fun i => ((hcsd _).mul hg).integrable_of_hasCompactSupport hgc.mul_left
  have hintR : ∀ i : Fin n,
      Integrable (fun x => f x * centralSecondDifference g (h • Pi.single i 1) x) := by
    intro i
    have hcg : Continuous (centralSecondDifference g (h • Pi.single i 1)) :=
      ((hg.comp (continuous_id.add continuous_const)).add
        (hg.comp (continuous_id.sub continuous_const))).sub (continuous_const.mul hg)
    refine (hf.mul hcg).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_left ?_
    have h1 := hgc.comp_homeomorph (Homeomorph.addRight (h • (Pi.single i 1 : Point n)))
    have h2 := hgc.comp_homeomorph (Homeomorph.subRight (h • (Pi.single i 1 : Point n)))
    have h3 : HasCompactSupport (fun x => 2 * g x) := hgc.mul_left
    exact (h1.add h2).sub h3
  have hL : (fun x => coordSecondDifference f h x * g x) =
      fun x => (h ^ 2)⁻¹ * ∑ i, centralSecondDifference f (h • Pi.single i 1) x * g x := by
    funext x
    rw [coordSecondDifference, mul_assoc, Finset.sum_mul]
  have hR : (fun x => f x * coordSecondDifference g h x) =
      fun x => (h ^ 2)⁻¹ * ∑ i, f x * centralSecondDifference g (h • Pi.single i 1) x := by
    funext x
    rw [coordSecondDifference, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hL, hR, integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun i _ => hintL i, integral_finsetSum _ fun i _ => hintR i]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    integral_centralSecondDifference_mul hf hg hgc _

end ViscositySolns
end
