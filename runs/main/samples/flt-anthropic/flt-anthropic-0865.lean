namespace P2MW.S_AlgebraicGeometry_ThetaLevel_forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open scoped BigOperators

open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

open AlgC4c in
theorem solution
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (γ : MulAut (Heis δ d)) (hγ : γ ∈ Heis.Gam δ d)
    (y₀ : HH δ) (hy₀ : IsUnit ((∑ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) (Pi.single y₀ 1)) y₀)) :
    (∀ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) (∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) =
        ∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) ∧
      Function.Bijective fun c : HH δ → B =>
        ∑ x : HH δ, c x • schrod δ d B ω (γ (Heis.theta x)) (∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) := by
  classical
  have hω2d : ω ^ (2 * d) = 1 := by rw [pow_mul, hω, hζ]
  set v : HH δ → B := ∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1) with hv

  have hmul : ∀ z z' : Heis δ d, schrod δ d B ω (γ (z * z')) = schrod δ d B ω (γ z) ∘ₗ schrod δ d B ω (γ z') := by
    intro z z'; rw [map_mul, schrod_mul δ d B ω hω2d]
  have hcen : ∀ a : ZMod (2 * d), schrod δ d B ω (γ (Heis.cen a)) = omegaPow d B ω a • LinearMap.id := by
    intro a; rw [hγ a, schrod_cen]

  have hfix : ∀ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) v = v := by
    intro k
    rw [hv, map_sum]
    have hterm : ∀ k', schrod δ d B ω (γ (Heis.eta k)) (schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) =
        schrod δ d B ω (γ (Heis.eta (k + k'))) (Pi.single y₀ 1) := by
      intro k'
      rw [← LinearMap.comp_apply, ← hmul, eta_mul_eta]
    simp_rw [hterm]
    exact Fintype.sum_equiv (Equiv.addLeft k) _ _ (fun k' => rfl)
  refine ⟨hfix, ?_⟩

  let Φ : (HH δ → B) →ₗ[B] (HH δ → B) :=
    ∑ x : HH δ, (LinearMap.proj x : (HH δ → B) →ₗ[B] B).smulRight (schrod δ d B ω (γ (Heis.theta x)) v)
  have hΦ : ∀ c : HH δ → B, Φ c = ∑ x : HH δ, c x • schrod δ d B ω (γ (Heis.theta x)) v := by
    intro c
    simp [Φ, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hΦ' : (fun c : HH δ → B => ∑ x : HH δ, c x • schrod δ d B ω (γ (Heis.theta x)) v) = ⇑Φ :=
    funext fun c => (hΦ c).symm
  rw [hΦ']

  have hstab : ∀ (w : Heis δ d) (c : HH δ → B), ∃ c' : HH δ → B, schrod δ d B ω (γ w) (Φ c) = Φ c' := by
    intro w c
    refine ⟨fun x' => omegaPow d B ω (w.a + pair δ d w.k (x' - w.h)) * c (x' - w.h), ?_⟩
    rw [hΦ, hΦ, map_sum]
    have key : ∀ x, schrod δ d B ω (γ w) (c x • schrod δ d B ω (γ (Heis.theta x)) v) =
        (omegaPow d B ω (w.a + pair δ d w.k x) * c x) • schrod δ d B ω (γ (Heis.theta (w.h + x))) v := by
      intro x
      rw [map_smul, ← LinearMap.comp_apply, ← hmul, mul_theta_eq, hmul, hmul, hcen, LinearMap.comp_apply,
        LinearMap.comp_apply, hfix, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, mul_comm]
    simp_rw [key]
    symm
    exact Fintype.sum_equiv (Equiv.subRight w.h) _ _ (fun x => by rw [Equiv.subRight_apply, add_sub_cancel])
  set W : Submodule B (HH δ → B) := LinearMap.range Φ with hW
  have hWstab : ∀ (z : Heis δ d) (u : HH δ → B), u ∈ W → schrod δ d B ω z u ∈ W := by
    intro z u hu
    obtain ⟨c, rfl⟩ := hu
    obtain ⟨c', hc'⟩ := hstab (γ.symm z) c
    rw [MulEquiv.apply_symm_apply] at hc'
    exact ⟨c', hc'.symm⟩

  have hvW : v ∈ W := by
    refine ⟨Pi.single 0 1, ?_⟩
    rw [hΦ, Fintype.sum_eq_single (0 : HH δ)]
    · rw [Pi.single_eq_same, one_smul, theta_zero, map_one, schrod_one, LinearMap.id_apply]
    · intro x hx; rw [Pi.single_eq_of_ne hx, zero_smul]

  have hproj : ∑ k : HH δ, thetaChar δ d B ω k (-y₀) • schrod δ d B ω (Heis.eta k) v =
      (((d : ℕ) : B) * v y₀) • Pi.single y₀ 1 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, schrod_eta_apply, smul_eq_mul]
    have : ∀ k, thetaChar δ d B ω k (-y₀) * (thetaChar δ d B ω k x * v x) = thetaChar δ d B ω k (x + -y₀) * v x := by
      intro k; rw [thetaChar_add_right δ d B ω hω2d]; ring
    simp_rw [this]
    rw [← Finset.sum_mul, sum_thetaChar δ d B ω hδd ζ hζ hζu hω]
    by_cases hx : x = y₀
    · subst hx; simp
    · rw [if_neg (fun h => hx (by rwa [← sub_eq_add_neg, sub_eq_zero] at h)), Pi.single_eq_of_ne hx, mul_zero,
        zero_mul]
  have hprojW : (((d : ℕ) : B) * v y₀) • (Pi.single y₀ 1 : HH δ → B) ∈ W := by
    rw [← hproj]
    exact W.sum_mem fun k _ => W.smul_mem _ (hWstab _ _ hvW)
  have hδ₀W : (Pi.single y₀ 1 : HH δ → B) ∈ W := by
    have hu : IsUnit (((d : ℕ) : B) * v y₀) := hd.mul (by simpa [hv] using hy₀)
    obtain ⟨b, hb⟩ := hu.exists_left_inv
    have : (Pi.single y₀ 1 : HH δ → B) = b • ((((d : ℕ) : B) * v y₀) • Pi.single y₀ 1) := by
      rw [smul_smul, hb, one_smul]
    rw [this]
    exact W.smul_mem b hprojW
  have hallW : ∀ y : HH δ, (Pi.single y 1 : HH δ → B) ∈ W := by
    intro y
    have : (Pi.single y 1 : HH δ → B) = schrod δ d B ω (Heis.theta (y - y₀)) (Pi.single y₀ 1) := by
      rw [schrod_theta_single]; congr 1; abel
    rw [this]
    exact hWstab _ _ hδ₀W
  have htop : W = ⊤ := by
    refine eq_top_iff.mpr fun c _ => ?_
    rw [← Finset.univ_sum_single c]
    refine W.sum_mem fun y _ => ?_
    have : (Pi.single y (c y) : HH δ → B) = c y • Pi.single y 1 := by
      funext x
      by_cases hx : x = y
      · subst hx; simp
      · simp [Pi.single_eq_of_ne hx]
    rw [this]
    exact W.smul_mem _ (hallW y)
  have hsurj : Function.Surjective Φ := LinearMap.range_eq_top.mp (hW ▸ htop)
  exact ⟨OrzechProperty.injective_of_surjective_endomorphism Φ hsurj, hsurj⟩

end P2MW.S_AlgebraicGeometry_ThetaLevel_forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply
