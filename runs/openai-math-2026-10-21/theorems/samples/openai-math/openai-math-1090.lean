namespace OAI

noncomputable section

open scoped Topology

open Filter

open Filter MeasureTheory

open UniformSpace

open scoped ContDiff

open UniformSpace

open Filter

open scoped Topology

open Filter MeasureTheory

open scoped Topology

namespace StronglyRationalVOA.SymmetricOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma timeAverage_strong_one (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hl : Tendsto r atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => timeAverage T hs (r n) x) atTop (𝓝 x) := by
  have hc := (StrongLimit.equicontinuous_of_norm_bound
    (fun n => timeAverage T hs (r n)) (fun n => timeAverage_norm T hs (hr n))).isClosed_setOfPred_tendsto
    (l := atTop) (f := id) continuous_id
  apply (closure_minimal (s := (T.domain : Set H)) (t := {x | Tendsto
    (fun n => timeAverage T hs (r n) x) atTop (𝓝 x)}) ?_ hc) (hs.dense_domain x)
  intro v hv
  let w : T.domain := ⟨v,hv⟩
  change Tendsto _ _ _
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm (a := fun n => r n*‖T w‖)
  · exact fun n => timeAverage_initial_bound T hs (T.mem_graph_iff.mpr ⟨w,rfl,rfl⟩) (hr n)
  · simpa only [zero_mul] using hl.mul_const ‖T w‖

end StronglyRationalVOA.SymmetricOperator
end
end OAI
