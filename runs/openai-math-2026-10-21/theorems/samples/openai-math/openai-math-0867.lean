namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup

open scoped TensorProduct

variable {L M σ X Ω J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] [Fintype Ω] [Fintype J]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {s t u d n : ℕ} (D : RationalFilteredNilmanifold L s d)
  (I : LieIdeal ℚ L) (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQ : Q.filtration = D.filtration.quotientLie I hI)

include hQ in

theorem exists_external_marked_quotient_restoration
    (G : NilpotentLieFiltration M u) (φ : L →ₗ⁅ℚ⁆ M)
    (hker : ∀ x ∈ I, φ x = 0) (htop : I.toSubmodule ≤ D.filtration.layer s)
    {w : σ → ℕ} (tests : X → D.Niltest w)
    (htests : ∀ x, (tests x).UnitIntervalValued)
    (quotientObservable : X → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup), quotientObservable x (QuotientGroup.mk
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) g)) =
      ((tests x).kernelProjection I.toSubmodule htop).observable (QuotientGroup.mk g))
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : G.realification.PolynomialOrbit w)
    (hmark : map ((realificationLieHom (quotientInducedMark I φ hker)).toLinearMap.restrictScalars ℚ)
      q.log = marked.log)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → σ → ℤ) (weight : X → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ j, ‖weight (physical a j)‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
      quotientObservable (physical a j) (QuotientGroup.mk
        (Q.filtration.realification.polynomialOrbitEval w (point a j) q)))).re) :
    ∃ restored : D.filtration.realification.PolynomialOrbit w,
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap restored.log = marked.log ∧
      (∀ x, ((tests x).withOrbit restored).observable = (tests x).observable ∧
        ((tests x).withOrbit restored).UnitIntervalValued ∧
        ∀ p, ((tests x).withOrbit restored).ComplexityLE p ↔ (tests x).ComplexityLE p) ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
        ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
          ((tests (physical a j)).withOrbit restored).eval (point a j))).re := by
  obtain ⟨g, hg, hm, _, _⟩ :=
    D.exists_prescribed_marked_quotientOrbit_lift I hI Q hQ φ hker G q marked hmark
  have hpoint (x : X) (z : σ → ℤ) :
      quotientObservable x (QuotientGroup.mk
        (Q.filtration.realification.polynomialOrbitEval w z q)) =
      (((tests x).kernelProjection I.toSubmodule htop).withOrbit g).eval z := by
    rw [← hg, D.quotientOrbit_eval I hI Q hQ]
    exact hrecovery x _
  have hs : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
      (((tests (physical a j)).kernelProjection I.toSubmodule htop).withOrbit g).eval
        (point a j))).re := by
    intro a ha
    simpa only [hpoint] using hscore a ha
  have hkernel : I.toSubmodule ≤ LinearMap.ker φ.toLinearMap := fun x hx => hker x hx
  obtain ⟨restored, hmarked, z, hz, hzmem, hzmap, htests', H', hsub, hpos, hmass, hfinal⟩ :=
    Niltest.exists_external_kernelProjection_prescribed_marked_orbit tests htests G φ
      I.toSubmodule htop hkernel g marked hm outer H hH localLaw physical point
      (fun a j => weight (physical a j)) hB hδ hweight hs
  refine ⟨restored, hmarked, ?_, H', hsub, hpos, hmass, hfinal⟩
  intro x
  exact ⟨(htests' x).1, (htests' x).2.2.2.1, (htests' x).2.2.2.2⟩

end Erdos3.RationalFilteredNilmanifold
end
end OAI
