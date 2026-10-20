public section

noncomputable section

open Function Set Topology WithLp

open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

variable [IsManifold (𝓡∂ (n + 1)) k M]

theorem exists_homeomorph_prod_Ico_of_mem_boundary (hk : k ≠ 0) {x : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M) :
    ∃ (U : Set M) (ε : ℝ), IsOpen U ∧ x ∈ U ∧ 0 < ε ∧
      Nonempty (↥U ≃ₜ ↥(U ∩ (𝓡∂ (n + 1)).boundary M) × ↥(Set.Ico (0 : ℝ) ε)) := by
  obtain ⟨φ, V, ε, hxφ, h⟩ := exists_isProductCollarChart_of_mem_boundary hk hx
  exact ⟨φ.source, ε, φ.open_source, hxφ, h.height_pos,
    ⟨h.homeomorphProd.trans
      ((Homeomorph.refl _).prodCongr (EuclideanHalfSpace.homeomorphNormalIio ε))⟩⟩

end TauCeti
end
end
