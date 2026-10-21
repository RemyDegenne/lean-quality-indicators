namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology

open MeasureTheory Filter Set

open scoped Topology

open MeasureTheory ProbabilityTheory Filter Set

namespace SKFluctuations.Hierarchy

open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar

open scoped Topology NNReal BigOperators

theorem scalarProfileJet_parameter_tendsto {α : ℕ → boundedMassProfiles}
    {β : boundedMassProfiles} (hα : Tendsto α atTop (𝓝 β))
    (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    TendstoUniformly (fun n => scalarProfileJet (boundedNonnegativeProfile (α n)) l t k)
      (scalarProfileJet (boundedNonnegativeProfile β) l t k) atTop := by
  apply jet_tendstoUniformly_of_limit
    (fun n j => scalarProfileJet (boundedNonnegativeProfile (α n)) l t j)
    (scalarProfileJet (boundedNonnegativeProfile β) l t)
    (fun n j x => scalarProfileJet_hasDerivAt _ (fun s => ((α n).property.1 s).2) l t j x)
    (fun j => ⟨(ReplicaTree.attachmentCount 1 j:ℝ),fun n x =>
      scalarProfileJet_bound _ (fun s => ((α n).property.1 s).2) l t j x⟩)
    (scalarProfileJet_hasDerivAt _ (fun s => (β.property.1 s).2) l t)
  have hh := scalarTerminal.profile_parameter_tendstoUniformly hα l t
  rw [Metric.tendstoUniformly_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε] with n hn x
  rw [scalarProfileJet_zero (boundedNonnegativeProfile β) (fun s => (β.property.1 s).2),
    scalarProfileJet_zero (boundedNonnegativeProfile (α n)) (fun s => ((α n).property.1 s).2)]
  exact hn (fun _ => x)

end SKFluctuations.Hierarchy
end
end OAI
