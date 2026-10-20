namespace P2MW.S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

section

section

section

noncomputable section

p2m_open

open scoped nonZeroDivisors Polynomial.Bivariate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace WeierstrassCurve

namespace Affine

p2m_open

universe u

variable {F : Type u} [Field F] [DecidableEq F] {W : Affine F}

variable [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W]

p2m_open

theorem isPrincipal_of_geomDivisorSum_eq_zero' [HasPrincipalDivisors F W.FunctionField]
    {D : AlgebraicCurve.Divisor F W.FunctionField} (h0 : Divisor.degree D = 0)
    (hD : geomDivisorSum D = 0) : Divisor.IsPrincipal D := by
  classical

  have hcls : ClassGroup.mk (K := W.FunctionField) (unitIdealOfDivisor D) = 1 := by
    rw [classGroup_mk_unitIdealOfDivisor, hD, _root_.map_zero]
    rfl

  obtain ⟨f, hf⟩ := (FractionalIdeal.isPrincipal_iff _).mp (ClassGroup.mk_eq_one_iff.mp hcls)
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hf
    exact Units.ne_zero (unitIdealOfDivisor D) hf

  have hfin : ∀ w : HeightOneSpectrum W.CoordinateRing,
      D (AlgebraicCurve.Place.ofHeightOneSpectrum (K := F) w)
        = (AlgebraicCurve.Place.ofHeightOneSpectrum (K := F) w).ord f := by
    intro w
    rw [← count_unitIdealOfDivisor, hf,
      AlgebraicCurve.Place.ord_ofHeightOneSpectrum_eq_count w hf0]

  obtain ⟨Df, hDf, hDf0⟩ := HasPrincipalDivisors.exists_divisor (K := F) f hf0

  have hsub : D - Df = Finsupp.single (InfinitePlace.place :
      AlgebraicCurve.Place F W.FunctionField) ((D - Df) InfinitePlace.place) := by
    ext v
    obtain ⟨P, rfl⟩ := geomPlaceOfPoint_surjective isElliptic_Δ_ne_zero v
    cases P with
    | zero =>
        rw [geomPlaceOfPoint_zero, Finsupp.single_eq_same]
    | some x y h =>
        rw [Finsupp.sub_apply, geomPlaceOfPoint_some, placeOfEquation, hfin, hDf, sub_self,
          Finsupp.single_apply, if_neg]
        exact infinitePlace_ne_ofHeightOneSpectrum _

  have hdeg : Divisor.degree (D - Df) = 0 := by rw [map_sub, h0, hDf0, sub_zero]
  rw [hsub, Divisor.degree_single, InfinitePlace.deg_eq_one, Nat.cast_one, mul_one,
    Finsupp.sub_apply, sub_eq_zero] at hdeg

  refine ⟨f, hf0, fun v => ?_⟩
  obtain ⟨P, rfl⟩ := geomPlaceOfPoint_surjective isElliptic_Δ_ne_zero v
  cases P with
  | zero => rw [geomPlaceOfPoint_zero, hdeg, hDf]
  | some x y h => rw [geomPlaceOfPoint_some, placeOfEquation, hfin]

end Affine
end WeierstrassCurve
end
end
end
end
end
end
end
end P2MW.S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
