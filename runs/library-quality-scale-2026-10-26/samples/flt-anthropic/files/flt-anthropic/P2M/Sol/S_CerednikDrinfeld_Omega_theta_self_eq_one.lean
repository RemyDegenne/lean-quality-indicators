import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_self
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_theta_self_eq_one

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ : K}
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    theta ρ a b z₀ z₀ = 1 := by
  rw [theta, show thetaFactor ρ a b z₀ z₀ = fun _ => 1 from funext fun γ =>
    CerednikDrinfeld.Omega.crossRatio_self z₀ _ _ (hz₀a γ).symm (hz₀b γ).symm]
  exact tprod_one
