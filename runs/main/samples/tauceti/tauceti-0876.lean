public section

noncomputable section

open Finset MeasureTheory Preorder ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

variable (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ]

@[simp]
theorem markovChainLaw_map_eval_zero :
    (markovChainLaw ν κ).map (fun x => x 0) = ν := by
  have hcomp : (fun x : ℕ → α => x 0)
      = (fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩) ∘ frestrictLe 0 := rfl
  have hid : (fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩) ∘
      (MeasurableEquiv.piUnique fun _ : ↥(Iic (0 : ℕ)) => α).symm = id := by
    funext a
    simp [MeasurableEquiv.piUnique, Equiv.piUnique, uniqueElim_const]
  calc (markovChainLaw ν κ).map (fun x => x 0)
      = ((markovChainLaw ν κ).map (frestrictLe 0)).map
          (fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩) := by
        rw [Measure.map_map (μ := markovChainLaw ν κ) (f := frestrictLe 0)
          (g := fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩)
          (by fun_prop) (measurable_frestrictLe 0), hcomp]
    _ = ν := by
        rw [markovChainLaw_map_frestrictLe_zero,
          Measure.map_map (μ := ν)
            (f := ⇑(MeasurableEquiv.piUnique fun _ : ↥(Iic (0 : ℕ)) => α).symm)
            (g := fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩)
            (by fun_prop) (MeasurableEquiv.measurable _), hid, Measure.map_id]

end Probability
end TauCeti
end
end
