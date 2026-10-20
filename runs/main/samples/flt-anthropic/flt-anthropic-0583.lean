namespace P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion

set_option Elab.async false

section Part_theta

namespace CellPeriods

p2m_open

open scoped Real Topology Manifold ContDiff

section LinearPath

variable {F : Type*} [Field F] [Algebra ℂ F]

variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]

variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

include hF in
theorem pathIntegral_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (θ : ι → Ω[F⁄ℂ])
    {P P' : Place ℂ F} (γ : Path P P')
    (hreg : ∀ i ∈ s, ∀ t, 0 ≤ (γ t).ordDifferential (θ i))
    (hprim : ∀ i ∈ s, ∃ g, IsPrimitiveAlong (θ i) γ g)
    (_hregsum : ∀ s' ⊆ s, ∀ t, 0 ≤ (γ t).ordDifferential (∑ i ∈ s', c i • θ i)) :
    (∃ g, IsPrimitiveAlong (∑ i ∈ s, c i • θ i) γ g) ∧
      pathIntegral (∑ i ∈ s, c i • θ i) γ = ∑ i ∈ s, c i * pathIntegral (θ i) γ :=
  AlgebraicCurve.pathIntegral_finset_sum_smul F hF ι s c θ γ hreg hprim

end LinearPath
end CellPeriods
end Part_theta
end P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues
