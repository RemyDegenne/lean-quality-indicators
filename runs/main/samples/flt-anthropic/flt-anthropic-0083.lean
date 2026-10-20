namespace P2MW.S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1

set_option autoImplicit false

open AlgebraicCurve ModularCurve

open scoped MatrixGroups

set_option maxHeartbeats 1600000 in
open GalIsoX1ClassImpl in
theorem solution
    (N : ℕ) [NeZero N]
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (n : ℕ) [NeZero n] (hpn : ¬ p ∣ n)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N)]
    (W : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N) n)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ Pl.inertiaSubgroupIn ℚ)
    (z y x : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N) n)
    (hyσ : σ • (y : ModularCurve.JOne N) = y)
    (hx : (x : ModularCurve.JOne N) = σ • (z : ModularCurve.JOne N) - z) :
    W.pair x y = 1 := by
  classical

  let g : SemilinearAut (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar N) := arithmeticGalois (x1FunctionField N) σ
  have hg : ∀ u : JOne N, σ • u = g • u := fun u => rfl
  have hgy : g • y = y := Subtype.ext (by rw [SemilinearAut.coe_torsion_smul, ← hg]; exact hyσ)
  have hxg : x = g • z - z := Subtype.ext (by rw [hx, hg, AddSubgroupClass.coe_sub, SemilinearAut.coe_torsion_smul])

  have hζ : W.pair z y ^ n = 1 := by
    rw [← GalIsoX1ClassImpl.pair_nsmul_left]
    have : n • z = 0 := Subtype.ext (by
      rw [AddSubgroupClass.coe_nsmul, ZeroMemClass.coe_zero]
      have hz := z.2
      rw [Pic0.mem_torsion, natCast_zsmul] at hz
      exact hz)
    rw [this, W.pair_zero_left]
  have hp : p.Prime := Fact.out
  have hσζ : σ (W.pair z y) = W.pair z y :=
    ValuationSubring.smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one Pl hp hPl hσ hpn hζ
  have h1 : W.pair (g • z) y = σ (W.pair z y) := by
    conv_lhs => rw [← hgy]
    rw [AlgebraicCurve.DivisorialWeilPairingData.pair_semilinearSmul]
    rfl
  rw [hxg, GalIsoX1ClassImpl.pair_sub_left, h1, hσζ, mul_inv_cancel₀ (W.pair_ne_zero z y)]

end P2MW.S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1
