open MeasureTheory

@[expose] public noncomputable section

theorem volume_posSimplex (α : Type*) [Fintype α] (r : ℝ) (hr : 0 ≤ r) :
    volume (posSimplex α r) =
      ENNReal.ofReal r ^ Fintype.card α / Nat.factorial (Fintype.card α) := by
  let σ : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let e : (Fin (Fintype.card α) → ℝ) ≃ᵐ (α → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) σ
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : α => ℝ) σ
  have he : e '' posSimplexFin (Fintype.card α) r = posSimplex α r := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨hy0, hys⟩
      refine ⟨?_, ?_⟩
      · intro i
        simpa [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using
          hy0 (σ.symm i)
      · simp only [e, MeasurableEquiv.coe_piCongrLeft]
        calc
          ∑ j, (Equiv.piCongrLeft (fun _ : α => ℝ) σ) y j =
              ∑ i, (Equiv.piCongrLeft (fun _ : α => ℝ) σ) y (σ i) :=
            (σ.sum_comp _).symm
          _ = ∑ i, y i := by
            apply Finset.sum_congr rfl
            intro i _
            exact Equiv.piCongrLeft_apply_apply (P := fun _ : α => ℝ) σ y i
          _ ≤ r := hys
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rcases hx with ⟨hx0, hxs⟩
      refine ⟨?_, ?_⟩
      · intro i
        have hp := congrFun (e.apply_symm_apply x) (σ i)
        have hp' : e.symm x i = x (σ i) := by
          calc
            e.symm x i = e (e.symm x) (σ i) := by
              simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
            _ = x (σ i) := hp
        rw [hp']
        exact hx0 (σ i)
      · have hp := e.apply_symm_apply x
        calc
          ∑ i, e.symm x i = ∑ j, e (e.symm x) j := by
            rw [← σ.sum_comp]
            simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
          _ = ∑ j, x j := by rw [hp]
          _ ≤ r := hxs
  calc
    volume (posSimplex α r) = volume (e '' posSimplexFin (Fintype.card α) r) := by rw [he]
    _ = volume (posSimplexFin (Fintype.card α) r) := by
      rw [← hmp.map_eq, Measure.map_apply e.measurable
        (e.measurableSet_image.2 (measurableSet_posSimplexFin _ _))]
      rw [e.preimage_image]
    _ = _ := volume_posSimplexFin _ _ hr

end
