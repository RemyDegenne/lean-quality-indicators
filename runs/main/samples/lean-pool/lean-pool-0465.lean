@[expose] public section

namespace LeanPool.PoincareThreeBody

open MeasureTheory Set

open scoped Interval

theorem hasDerivAt_resonantDisturbingFunction_time_actionPoisson
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    HasDerivAt (resonantDisturbingFunction p q eccentricity orientation)
      (dot (delaunayFrequency (resonantFirstAction p q))
        (resonantPerturbationActionPoisson
          p q eccentricity orientation time)) time := by
  let state := orientedResonantKeplerPhasePoint p q eccentricity orientation time
  have hperturbation : DifferentiableAt ℝ firstMassPerturbation state :=
    differentiableAt_firstMassPerturbation_orientedResonantKeplerPhasePoint
      hp hq heccentricity heccentricityOne hapoapsis
  have htime := DifferentiableAt.hasDerivAt_comp_orientedResonantKeplerPhasePoint
    hp hq heccentricity heccentricityOne hperturbation
  have hcollision : (0, state) ∈ collisionFree :=
    orientedResonantKeplerPhasePoint_collisionFree_mass_zero hp hq heccentricity
      heccentricityOne hapoapsis
  have hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0 := by
    simpa [secondPrimaryDistanceSq] using hcollision.2
  have hstateLifted : state = liftedDelaunayPhasePoint
      (resonantFirstAction p q) eccentricity (resonantMeanAnomaly p q time)
      (orientation - time) :=
    (liftedDelaunayPhasePoint_resonant hp hq eccentricity orientation time).symm
  have henergyIdentity : cartesianKeplerEnergy state =
      -1 / (2 * resonantFirstAction p q ^ 2) := by
    rw [hstateLifted]
    exact cartesianKeplerEnergy_liftedDelaunayPhasePoint
      (resonantFirstAction_pos hp hq).ne' heccentricity heccentricityOne
  have henergy : cartesianKeplerEnergy state < 0 := by
    rw [henergyIdentity]
    exact div_neg_of_neg_of_pos (by norm_num)
      (mul_pos (by norm_num) (sq_pos_of_pos (resonantFirstAction_pos hp hq)))
  have hbracket := poissonBracket_hamiltonian_zero_eq_frequency_dot_actionPoisson
    hposition henergy firstMassPerturbation
  have hfirstActionIdentity : cartesianDelaunayActions state 0 =
      resonantFirstAction p q := by
    rw [hstateLifted, cartesianDelaunayActions_liftedDelaunayPhasePoint
      (resonantFirstAction_pos hp hq) heccentricity heccentricityOne]
    rfl
  rw [hfirstActionIdentity] at hbracket
  have htimeFrequency : HasDerivAt
      (fun argument ↦ firstMassPerturbation
        (orientedResonantKeplerPhasePoint p q eccentricity orientation argument))
      (dot (delaunayFrequency (resonantFirstAction p q))
        (resonantPerturbationActionPoisson p q eccentricity orientation time)) time := by
    apply htime.congr_deriv
    simpa [state, resonantPerturbationActionPoisson] using hbracket
  have hfunction : (fun argument ↦ firstMassPerturbation
      (orientedResonantKeplerPhasePoint p q eccentricity orientation argument)) =
      resonantDisturbingFunction p q eccentricity orientation := by
    funext argument
    exact firstMassPerturbation_orientedResonantKeplerPhasePoint
      p q eccentricity orientation argument
  rw [← hfunction]
  exact htimeFrequency

end LeanPool.PoincareThreeBody
end
