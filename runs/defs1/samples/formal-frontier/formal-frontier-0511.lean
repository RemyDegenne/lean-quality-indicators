@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- Stereographic coordinates on the south-punctured sphere. -/
noncomputable def sphere2SouthPuncturedHomeomorph :
    ((TopologicalSpace.Opens.toTopCat sphere2).obj sphere2SouthPunctured : Type) ≃ₜ
      EuclideanSpace ℝ (Fin 2) := by
  letI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  exact (Homeomorph.setCongr (by simp [sphere2SouthPunctured])).trans
    (stereographic' 2 sphere2SouthPoint).toHomeomorphSourceTarget |>.trans
    (Homeomorph.setCongr (stereographic'_target sphere2SouthPoint)) |>.trans
    (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 2)))

end SphereTopology
end
end
