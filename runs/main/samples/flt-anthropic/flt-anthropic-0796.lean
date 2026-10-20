namespace P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion

set_option Elab.async false

section Part_g2prims

namespace CellPeriods

p2m_open

open scoped Real Topology Manifold ContDiff

section G2Prims

variable {F : Type*} [Field F] [Algebra ℂ F]

variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]

variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

variable {R : Type*}

variable (𝒟 : AlgebraicCurve.CellDissection F) (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])

variable {𝒟 S}

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem PolePos.center (hS : PolePos 𝒟 S) {v : Place ℂ F} (hv : v ∈ S) {C : 𝒟.ιC}
    (hvC : v ∈ (𝒟.cell C).carrier) : v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q := by
  obtain ⟨C', hC', hq⟩ := hS.hd5 v hv
  obtain rfl := eq_of_mem_interior'' hC' hvC
  exact ⟨hC', hq⟩

end G2Prims
end CellPeriods
end Part_g2prims
end P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues
