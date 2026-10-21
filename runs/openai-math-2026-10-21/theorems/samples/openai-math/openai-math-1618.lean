namespace OAI

noncomputable section

open MeasureTheory Set Filter

open scoped Topology ComplexConjugate

namespace PlanarEndpoint

lemma integral_affineScale {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Plane → V) (x₀ : Plane) {r : ℝ} (hr : 0 < r) :
    (∫ x, f x) = r^2 • ∫ X, f (affineScale x₀ r X) := by
  change _ = r^2 • ∫ X, (fun x => f (x₀+x)) (r • X)
  rw [Measure.integral_comp_smul_of_nonneg (volume : Measure Plane) (fun x => f (x₀+x)) r (hR := hr.le)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, integral_add_left_eq_self,
    smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_smul]

end PlanarEndpoint
end
end OAI
