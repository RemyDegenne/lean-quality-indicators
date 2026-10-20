namespace P2MW.S_ModularCurve_isGamma0PowAt_tateBase_prod_X_sub_C_toricPoint_fst

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

universe u

p2m_reactivate

open Polynomial in
theorem solution
    (F : Type u) [Field F] (p k : ℕ) [Fact p.Prime] (ζ : F) (hζ : IsPrimitiveRoot ζ (p ^ k))
    (n : ℕ) [NeZero n] :
    ModularCurve.IsGamma0PowAt (ModularCurve.tateBase F n) p k
      (∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
        (X - C (ModularCurve.toricPoint F n (ζ ^ a)).1)) := by
  classical
  have hp : p.Prime := Fact.out
  have hNpos : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  obtain ⟨P, hPN, hPa⟩ := P2MTateGenKernel.exists_point ζ hζ hNpos

  have hidx : ∀ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), ¬ p ^ k ∣ a := by
    intro a ha h
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    have := Nat.le_of_dvd (by omega) h
    have : p ^ k / 2 < p ^ k := Nat.div_lt_self (by omega) one_lt_two
    omega
  have hW₁ : ModularCurve.IsGamma0PowAt (P2MTateGenKernel.W₁ F) p k
      (∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), (X - C (ModularCurve.toricPoint F 1 (ζ ^ a)).1)) := by
    have hprod : (∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), (X - C (ModularCurve.toricPoint F 1 (ζ ^ a)).1)) =
        ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), (X - C ((a • P).coordsOrZero).1) := by
      refine Finset.prod_congr rfl fun a ha => ?_
      rw [hPa a (hidx a ha)]
    rw [hprod]
    by_cases hpk : p ^ k = 2
    · rw [ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk]
      have hset : (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a) = {1} := by
        have hp2 : p = 2 := by
          have h2 : p ∣ 2 := by rw [← hpk]; exact dvd_pow_self p (by rintro rfl; simp at hpk)
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
        rw [hpk]
        ext a
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, hp2]
        omega
      rw [hset, Finset.prod_singleton, one_smul]
      rw [hpk] at hPN
      exact WeierstrassCurve.isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two _ P hPN
    · rw [ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk]
      exact WeierstrassCurve.isCyclicGenKernel_prod_X_sub_C_coordsOrZero_nsmul_of_addOrderOf_eq_pow _ p k hpk P hPN

  have hmap := ModularCurve.IsGamma0PowAt.map (ModularCurve.qExpand F n) (P2MTateGenKernel.W₁ F) p k hW₁
  rw [P2MTateGenKernel.W₁_map_qExpand, Polynomial.map_prod] at hmap
  convert hmap using 2 with a ha
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, P2MTateGenKernel.toricPoint_fst_eq_qExpand]

end P2MW.S_ModularCurve_isGamma0PowAt_tateBase_prod_X_sub_C_toricPoint_fst
