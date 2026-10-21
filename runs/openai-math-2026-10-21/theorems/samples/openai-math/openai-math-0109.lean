namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder

open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma slabWidth_bounds {d : ℕ} (v : Fin d → ℝ) (hv : ∀ i, |v i| ≤ 1)
    (γ : Word d) (hγ : RegenerationWord v γ) :
    0 < slabWidth v γ ∧ slabWidth v γ ≤ (slabRecords v γ : ℝ) := by
  have hz : height v (wordPath γ 0) = 0 := by rw [hγ.2.1,height_zero]
  refine ⟨?_,height_le_recordCount v (wordPath γ) γ.1 hz ?_ γ.1 le_rfl⟩
  · have h := (hγ.2.2.2.1 0 hγ.1).2
    rwa [hz] at h
  · intro i hi
    obtain ⟨e,he⟩ := hγ.2.2.1 i hi
    rw [he,height_add]
    linarith [height_stepVector_le_one v hv e]

end DirectionalZeroOne
end OAI
