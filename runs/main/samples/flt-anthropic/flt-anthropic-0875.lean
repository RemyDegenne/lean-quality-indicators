namespace P2MW.S_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation

attribute [-instance] ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option linter.unusedSectionVars false

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hp : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hmem : ModularCurve.modularUnitSeries p ∈ ModularCurve.modularFunctionFieldFull (N * p))
    (R₀ : AlgebraicCurve.RegularProlongation A (ModularCurve.modularFunctionFieldBar (N * p))
      (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))

    (h₀ : ∀ (y : LaurentSeries A)
      (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar (N * p)),
      ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
          ModularCurve.modularFunctionFieldBar (N * p)) ∈ R₀.integers,
        (((R₀.residue ⟨_, hint⟩ :
            ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) :
            LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.coeffMap (IsLocalRing.residue A) y)
    [DecidableEq (IsLocalRing.ResidueField A)] (S₀ : Finset (IsLocalRing.ResidueField A))
    (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ModularCurve.ssJSet p (IsLocalRing.ResidueField A)) :
    ∃ hu₀ : (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.modularUnitSeries p),
          ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ :
          ModularCurve.modularFunctionFieldBar (N * p)) ∈ R₀.integers,
      (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.modularUnitSeries p),
          ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ :
          ModularCurve.modularFunctionFieldBar (N * p))⁻¹ ∈ R₀.integers ∧
      (((R₀.residue ⟨_, hu₀⟩ :
          ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        ∏ a ∈ S₀, (ModularCurve.jqModC (IsLocalRing.ResidueField A) - HahnSeries.C a) ^
          (12 / ModularCurve.jWidth a) :=
  LigozatUnitSS.main N p A hp hA hmem R₀ h₀ S₀ hS₀

end P2MW.S_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation
