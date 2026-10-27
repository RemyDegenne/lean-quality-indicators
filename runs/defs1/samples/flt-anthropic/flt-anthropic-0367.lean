namespace P2MW.S_ModularCurve_exists_chartData_of_lineResidues

attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

set_option autoImplicit false

set_option linter.unusedSectionVars false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

namespace LineResidues

section Generic

open Classical

variable
    {A : ValuationSubring (AlgebraicClosure ℚ)} [DecidableEq (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] [HasPrincipalDivisors (AlgebraicClosure ℚ) F]
    (hFrat : ∀ P : Place (AlgebraicClosure ℚ) F, P.IsRational)
    (C : ComponentChart A F ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
    {r : ℕ} (s : Fin r → F) (hint : ∀ l, s l ∈ C.integers) (hunit : ∀ l, C.residue ⟨s l, hint l⟩ ≠ 0)

    (D : Polynomial (IsLocalRing.ResidueField ↥A)) (R : Fin r → Polynomial (IsLocalRing.ResidueField ↥A)) (hD : D ≠ 0)
    (hR : ∀ l, (C.residue ⟨s l, hint l⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) D
      = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R l))

    (c₀ : Place (AlgebraicClosure ℚ) F) (hc₀ : c₀ ∈ C.dom)
    (hc₀inf : C.placeMap c₀ = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))
    (hreg₀ : ∀ P ∈ C.dom, P ≠ c₀ → ∀ l, s l ∈ P.toValuationSubring)

    (hdom : ∀ P ∈ C.dom, (∃ x₀ : IsLocalRing.ResidueField ↥A, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ ∧ D.eval x₀ ≠ 0) ∨
      C.placeMap P = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))

    (hcusp : ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) F, (∀ W, E W = W.ord f) →
        Finsupp.mapDomain C.placeMap
            (E.filter (fun W => W ∈ C.dom ∧ C.placeMap W = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))))
            (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))
          = (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (C.residue ⟨f, hf⟩))

    (c i : IsLocalRing.ResidueField ↥A → Fin r) (H : Finset (Fin r))
    (hcx : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → (R (c x₀)).eval x₀ ≠ 0)
    (hix : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      (R (i x₀) * Polynomial.C ((R (c x₀)).eval x₀) - R (c x₀) * Polynomial.C ((R (i x₀)).eval x₀)).rootMultiplicity x₀ = 1)
    (hsepx : ∀ P ∈ C.dom, ∀ Q ∈ C.dom, ∀ x₀ y₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → C.placeMap Q = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) y₀ → x₀ ≠ y₀ →
      ∃ a b, (R a).eval x₀ * (R b).eval y₀ ≠ (R b).eval x₀ * (R a).eval y₀)
    (hHx : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → ∃ l ∈ H, (R l).eval x₀ ≠ 0)

    (cInf iInf : Fin r) (hcInf : ∀ l, (R l).natDegree ≤ (R cInf).natDegree) (hcInfD : D.natDegree ≤ (R cInf).natDegree) (hcInfH : cInf ∈ H)
    (hpole : ∀ l, -(((R cInf).natDegree - D.natDegree : ℕ) : ℤ) ≤ c₀.ord (s l))
    (hiInf : (R iInf - Polynomial.C ((R iInf).coeff (R cInf).natDegree / (R cInf).leadingCoeff) * R cInf).natDegree + 1
      = (R cInf).natDegree)
    (hiInf0 : R iInf - Polynomial.C ((R iInf).coeff (R cInf).natDegree / (R cInf).leadingCoeff) * R cInf ≠ 0)
    (hsepInf : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      ∃ a b, (R a).eval x₀ * ((R b).coeff (R cInf).natDegree / (R cInf).leadingCoeff)
        ≠ (R b).eval x₀ * ((R a).coeff (R cInf).natDegree / (R cInf).leadingCoeff))

noncomputable def idxOf (g : IsLocalRing.ResidueField ↥A → Fin r) (gInf : Fin r) (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : Fin r :=
  if v = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) then gInf else g (xOf (A := A) v)

end Generic
end LineResidues
end P2MW.S_ModularCurve_exists_chartData_of_lineResidues
