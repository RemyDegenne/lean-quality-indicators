namespace OAI

universe uF

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace GaussianPropeller

open scoped RealInnerProductSpace

theorem sum_centroid_eq_zero {d k : ℕ} {A : Fin k → Set (Space d)}
    (hA : IsPartition A) : ∑ i, centroid (A i) = 0 := by
  have hi (i : Fin k) : Integrable ((A i).indicator (fun x => x)) (gaussian d) :=
    (integrable_id_gaussian d).indicator (hA.1 i)
  calc
    ∑ i, centroid (A i) = ∑ i, ∫ x, (A i).indicator (fun x => x) x ∂gaussian d := by
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_indicator (hA.1 i)).symm
    _ = ∫ x, ∑ i, (A i).indicator (fun x => x) x ∂gaussian d :=
      (integral_finsetSum _ (fun i _ => hi i)).symm
    _ = ∫ x, x ∂gaussian d := integral_congr_ae (sum_indicator_eq hA (fun x => x))
    _ = 0 := integral_id_stdGaussian

end GaussianPropeller
end OAI
