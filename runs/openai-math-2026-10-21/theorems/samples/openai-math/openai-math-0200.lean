namespace OAI

section

namespace SharpLogRamsey.PivotGeometry

open Finset Real Incidence Validation GeometricCover

open scoped Classical BigOperators

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma incidence_mono {A S : Finset (Projectivization K V)}
    {B T : Finset (Projectivization K (Module.Dual K V))} (hS : S⊆A) (hT : T⊆B) :
    incidenceCount S T≤ incidenceCount A B := by
  apply (sum_le_sum (fun y (_ : y∈T) => card_le_card (filter_subset_filter _ hS))).trans
  exact sum_le_sum_of_subset_of_nonneg hT (by intros; exact Nat.zero_le _)

end
end SharpLogRamsey.PivotGeometry
end
end OAI
