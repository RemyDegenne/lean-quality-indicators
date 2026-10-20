namespace P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy

set_option autoImplicit false

noncomputable section

p2m_open

namespace AlgebraicCurve

p2m_open

namespace BaseChangeTwo

section Main

variable {K F F₁ F₂ Z Z' : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
  [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [Algebra K Z']
  [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂]
  [HasPrincipalDivisors K Z] [HasPrincipalDivisors K Z']
  (φ : F →ₐ[K] F₁) (ψ' : F →ₐ[K] F₂)
  (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z) (s : F₁ →ₐ[K] Z') (s' : F₂ →ₐ[K] Z')
  (hsq : u.comp φ = u'.comp ψ') (hsq' : s.comp φ = s'.comp ψ')
  (hφ : φ.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral)
  (hu : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral)
  (hs : s.toRingHom.IsIntegral) (hs' : s'.toRingHom.IsIntegral)
  (hψ'fin : FiniteAlong K ψ') (hufin : FiniteAlong K u) (hsfin : FiniteAlong K s)
  (hNψ' : NormFormulaAlong K ψ' hψ'fin) (hNu : NormFormulaAlong K u hufin)
  (hNs : NormFormulaAlong K s hsfin)
  (hgen : IntermediateField.adjoin K (Set.range u ∪ Set.range u') = ⊤)
  (hgen' : IntermediateField.adjoin K (Set.range s ∪ Set.range s') = ⊤)
  (hdeg : finrankAlong K u + finrankAlong K s = finrankAlong K ψ')
  (hne : ∃ (a : F₁) (b : F₂), s a = s' b ∧ u a ≠ u' b)

omit [HasPrincipalDivisors K F₂] in
include hsq hsq' hψ'fin hufin hsfin hNψ' hNu hNs hgen hgen' hdeg hne in

theorem lhs_eq_rhs_of_forall_eq_ord {g : F₂} (hg : g ≠ 0) {D : Divisor K F₂}
    (hD : ∀ v : Place K F₂, D v = v.ord g) :
    lhs φ ψ' hφ hψ' D = rhs u u' s s' hu hu' hs hs' D := by
  ext w₁

  have h1 : ∀ v : Place K F, Divisor.pushforwardAlong ψ' hψ' D v =
      v.ord (letI := algebraAlong ψ'; Algebra.norm F g) :=
    fun v => pushforwardAlong_apply_eq_ord ψ' hψ' hψ'fin hNψ' hg hD v
  have hL : lhs φ ψ' hφ hψ' D w₁ = w₁.ord (φ (letI := algebraAlong ψ'; Algebra.norm F g)) := by
    show Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D) w₁ = _
    exact pullbackAlong_apply_eq_ord φ hφ h1 w₁

  have hu'g : u' g ≠ 0 := (map_ne_zero u').mpr hg
  have hs'g : s' g ≠ 0 := (map_ne_zero s').mpr hg
  have hR₁ : Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D) w₁ =
      w₁.ord (letI := algebraAlong u; Algebra.norm F₁ (u' g)) :=
    pushforwardAlong_apply_eq_ord u hu hufin hNu hu'g
      (fun z => pullbackAlong_apply_eq_ord u' hu' hD z) w₁
  have hR₂ : Divisor.pushforwardAlong s hs (Divisor.pullbackAlong s' hs' D) w₁ =
      w₁.ord (letI := algebraAlong s; Algebra.norm F₁ (s' g)) :=
    pushforwardAlong_apply_eq_ord s hs hsfin hNs hs'g
      (fun z => pullbackAlong_apply_eq_ord s' hs' hD z) w₁
  have hR : rhs u u' s s' hu hu' hs hs' D w₁ =
      w₁.ord (letI := algebraAlong u; Algebra.norm F₁ (u' g)) +
        w₁.ord (letI := algebraAlong s; Algebra.norm F₁ (s' g)) := by
    show (Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D) +
      Divisor.pushforwardAlong s hs (Divisor.pullbackAlong s' hs' D)) w₁ = _
    rw [Finsupp.add_apply, hR₁, hR₂]
  rw [hL, hR, map_norm_eq_norm_mul_norm φ ψ' u u' s s' hsq hsq' hψ'fin hufin hsfin hgen hgen' hdeg hne g]
  exact Place.ord_mul _ (norm_along_ne_zero u hufin hu'g) (norm_along_ne_zero s hsfin hs'g)

end Main
end BaseChangeTwo
end AlgebraicCurve
end
end P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong
