namespace OAI

section

section

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma cmc_symbol_lipschitz {p : Plane → Plane} {K : ℝ≥0}
    (hp : LipschitzWith K p) (hpb : ∀ y,‖p y‖≤1) :
    ∃ L : ℝ≥0,LipschitzWith L (fun y ↦ cmcJacobian (p y)) := by
  obtain ⟨L,hL,hLip⟩ := cmcJacobian_uniform_lipschitz
  let L' : ℝ≥0 := ⟨L*(K:ℝ),mul_nonneg hL K.coe_nonneg⟩
  refine ⟨L',?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ ≤ L*dist (p x) (p y) := by simpa only [dist_eq_norm] using hLip (p x) (p y) (hpb x) (hpb y)
    _ ≤ L*((K:ℝ)*dist x y) := mul_le_mul_of_nonneg_left (hp.dist_le_mul x y) hL
    _ = _ := by change L*((K:ℝ)*dist x y)=L*(K:ℝ)*dist x y; ring

end CubicTorus
end
end
end
end OAI
