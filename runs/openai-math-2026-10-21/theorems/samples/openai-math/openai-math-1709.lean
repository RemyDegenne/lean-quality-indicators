namespace OAI

noncomputable section

open MeasureTheory Filter

open scoped Topology BigOperators ContDiff

open MeasureTheory Filter

open scoped Topology BigOperators InnerProductSpace

namespace CoulombAtom

open CoulombObservation

attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator

theorem quantum_near_minimizer_lipschitz_ims {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    (p : FermionLipschitzMultiplier N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      formEnergy Z (graphFormVector (p.apply F)) ≤
        energy Z N * ‖fermionGraphValue N (p.apply F)‖^2 +
        (1/2:ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
          ∫ x, (lineDeriv ℝ p.value x (direction i a))^2 *
            ‖graphComponent s none F x‖^2) + δ := by
  apply Exists.imp (p := fun F : fermionGraph N =>
      ‖fermionGraphValue N F‖^2 = 1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      (⟪p.apply (p.apply F),sectorExcessOperator Z N F⟫_ℂ).re ≤ δ)
  · intro F h
    refine ⟨h.1,h.2.1,?_⟩
    have hi := quantum_lipschitz_ims_residual Z F p
    have hr := h.2.2
    linarith only [hi,hr]
  · exact quantum_approximate_double_lipschitz hZ N p hδ

end CoulombAtom
end
end OAI
