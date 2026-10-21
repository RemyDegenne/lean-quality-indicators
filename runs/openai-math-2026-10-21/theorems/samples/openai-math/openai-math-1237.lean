namespace OAI

noncomputable section

open scoped Classical BigOperators Topology

open Complex Set MeasureTheory Filter

namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss

open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues

open PrincipalMellinGrowth ProbeMellinBoundary

local notation "Id" => Ideal ActualEisensteinCubic.O

local instance : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

local instance : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable

theorem source_z_boundary_any {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0⊆Icc a0 b0) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s : ℂ) (hs : 7/8≤s.re) (hη : LFunction (η.excludePrimes S hS.prime) s≠0)
    {e : ℝ} (he : 0<e) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)) (33/200) (1/6+e) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 (∏P∈S,P)
    X Y Z hX hZ (η.excludePrimes S hS.prime) s hη
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) (AL := zBoxAmplitude (∏P∈S,P) (1/6+e))
    he (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _))
    (zBoxAmplitude_nonneg _ _) 0 3
  · exact (combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)<z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound η S hS.tail J T b hT s
      1 ((x:ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)
  · intro x hx t _
    exact fixed_principal_z_box_growth (∏P∈S,P) (1/6+e) x t hx

end SevenEighths.ProbePrincipalContours
end
end OAI
