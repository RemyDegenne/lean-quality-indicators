namespace P2MW.S_ModularCurve_B3_exists_variableChange_specialFibre_goodModel

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

open scoped Classical

noncomputable section

p2m_open

namespace ModularCurve

namespace B3

p2m_open

open ModularCurve.TatePoint

scoped instance instCharZeroH : CharZero H :=
  charZero_of_injective_algebraMap (algebraMap Qbar H).injective

local notation "ι" => (HahnSeries.ofPowerSeries ℚ Qbar)

universe u

scoped instance instIsElliptic_goodModel (j₀ : Qbar) : (goodModel j₀).IsElliptic := by
  unfold goodModel; infer_instance

private scoped instance isElliptic_specialFibre_goodModel (j₀ : Qbar) :
    (specialFibre (goodModel j₀)).IsElliptic := by
  by_cases h0 : j₀ = 0
  · subst h0; obtain ⟨hE, -⟩ := goodModel_zero_spec.2.2; exact hE
  · by_cases h1728 : j₀ = 1728
    · subst h1728; obtain ⟨hE, -⟩ := goodModel_1728_spec.2.2; exact hE
    · rw [(goodModel_generic_spec j₀ h0 h1728).2.2]; infer_instance

variable {K : Type*} [Field K]

scoped instance isShortNF_a6Model (B : K) : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve K).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

scoped instance isShortNF_a4Model (A : K) : (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve K).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

section H6B

open WeierstrassCurve.Affine

theorem redPoint_monodromy_cocycle_1728 (m : H ≃ₐ[Qbar] H)
    (hm : m ∈ HahnSeries.monodromy Qbar) (ζ : Qbar)
    (hζs : m (HahnSeries.single (3 / 4 : ℚ) 1) = HahnSeries.single (3 / 4 : ℚ) ζ)
    (hE : (nearCurve 1728).map (m : H →+* H) = nearCurve 1728)
    {x y : H} (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop)
    (h : (goodModel 1728).toAffine.Nonsingular x y) :
    redPoint (goodModel 1728) (goodModel_spec 1728).1 (goodModel_spec 1728).2
        (scaleAddEquiv 1728 (WeierstrassCurve.Affine.Point.fixedTransport m (nearCurve 1728) hE
          ((scaleAddEquiv 1728).symm (WeierstrassCurve.Affine.Point.some x y h)))) =
      WeierstrassCurve.Affine.Point.some (ζ ^ 2 * x.coeff 0) (ζ ^ 3 * y.coeff 0)
        (nonsingular_cocycle_1728 m hm hζs hx hy h) := by
  rw [fixedTransport_conj_1728 m hm ζ hζs hE h]
  have hCint : 0 ≤ (HahnSeries.C ζ : H).orderTop := by
    rw [← HahnSeries.ofPowerSeries_C]
    exact orderTop_ofPowerSeries_nonneg _
  have hmx : 0 ≤ (m x).orderTop := by
    rw [orderTop_of_mem_monodromy hm]
    exact hx
  have hmy : 0 ≤ (m y).orderTop := by
    rw [orderTop_of_mem_monodromy hm]
    exact hy
  rw [redPoint_some _ _ _ (orderTop_mul_nonneg (orderTop_pow_nonneg hCint 2) hmx)
    (orderTop_mul_nonneg (orderTop_pow_nonneg hCint 3) hmy) _]
  refine some_point_ext ?_ ?_
  · rw [coeff_zero_mul_of_integral (orderTop_pow_nonneg hCint 2) hmx,
      coeff_zero_of_mem_monodromy hm, ← map_pow, coeff_zero_C]
  · rw [coeff_zero_mul_of_integral (orderTop_pow_nonneg hCint 3) hmy,
      coeff_zero_of_mem_monodromy hm, ← map_pow, coeff_zero_C]

end H6B
end B3
end ModularCurve
end
end P2MW.S_ModularCurve_B3_exists_variableChange_specialFibre_goodModel
