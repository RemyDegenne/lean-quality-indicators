public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

open CFSG.LieType.Steinberg (sl2Upper sl2Lower)

open CFSG.LieType.Steinberg.Sp (blockMat)

open scoped MatrixGroups

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

open CFSG.ClassicalInvolution.WeakCT (diagConj2)

open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

open CFSG.ClassicalInvolution.RouteD (le_of_perfect_of_le_sup_center ker_proj_eq_center)

open CFSG.ClassicalInvolution.RouteD.SpAdapt

open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)

open CFSG.ClassicalInvolution.Q3.Q3Z (orderOf_not_dvd_three_of_center_sp)

open CFSG.ClassicalInvolution.Q3.Q3TPS (ringChar_galoisField_three_ne_two sl2Upper_pow_three
  sl2Lower_pow_three)

local notation "F₃" => GaloisField 3 1

theorem f4AdaptFact3 :
    ∀ {X : Type} [Group X] (ψ : StatedSp 3 (GaloisField 3 1) →* X),
      ψ.ker ≤ Subgroup.center (StatedSp 3 (GaloisField 3 1)) → ψ.range.Normal →
      ∀ τ : X ≃* X, (∀ x, τ (τ x) = x) → ∀ θ : SL(2, GaloisField 3 1) →* X,
        θ.range = (longBlock (GaloisField 3 1) 3 2).range.map ψ →
        (∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) →
        ∃ g : StatedSp 3 (GaloisField 3 1),
          (longBlock (GaloisField 3 1) 3 2).range.map (MulAut.conj g).toMonoidHom =
              (longBlock (GaloisField 3 1) 3 2).range ∧
            (∀ x ∈ (shortBlock (GaloisField 3 1) (by decide : (1 : Fin 3) ≠ 2)).range.map
                (MulAut.conj g).toMonoidHom, τ (ψ x) = ψ x) ∧
            ∀ x ∈ (shortBlock (GaloisField 3 1) (by decide : (0 : Fin 3) ≠ 1)).range.map
                (MulAut.conj g).toMonoidHom, τ (ψ x) = ψ x := by
  intro X _ ψ hker hnorm τ hτ θ hθ hθτ
  classical
  have h2 : (2 : F₃) ≠ 0 := Ring.two_ne_zero ringChar_galoisField_three_ne_two
  have hPsp : Group.IsPerfect (StatedSp 3 F₃) := Q3V.Lift.isPerfect_sp_three (by norm_num)
  have hstab := stab_of_normal_sp6 ψ hnorm τ θ hθ hθτ
  obtain ⟨A, σ, hAσ⟩ := exists_semilinear_lift_sp6 ψ hker τ hτ hstab
  let ρ : StatedSp 3 F₃ ≃* StatedSp 3 F₃ := (fieldSp 3 F₃ σ).trans (conjSp 3 F₃ A)
  have hρψ : ∀ x, ψ (ρ x) = τ (ψ x) := fun x => (hAσ x).symm
  obtain ⟨γ, hγθ⟩ := exists_gamma ψ hker θ hθ
  have hρL := rho_mem_longBlock_sp6 ψ hker τ θ hθ hθτ ρ hρψ
  have hρρ : ∀ x : StatedSp 3 F₃,
      conjSp 3 F₃ A (fieldSp 3 F₃ σ (conjSp 3 F₃ A (fieldSp 3 F₃ σ x))) = x :=
    rho_rho ψ hker τ hτ hPsp ρ hρψ
  have hD := comm_longInv_of_rho A σ (rho_longInv h2 ρ hρL)
  have hsq := sq_scalar_of_rho A σ hρρ
  set Am : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F₃ :=
    ((A : GL (Fin 3 ⊕ Fin 3) F₃) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F₃) with hAm
  set Bm : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F₃ :=
    (((A : GL (Fin 3 ⊕ Fin 3) F₃)⁻¹ : GL (Fin 3 ⊕ Fin 3) F₃) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F₃) with hBm
  have hAB : Am * Bm = 1 := by
    rw [hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : Bm * Am = 1 := by
    rw [hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hsim : ∀ u v, form (Am *ᵥ u) (Am *ᵥ v) = ((multiplier 3 F₃ A : F₃ˣ) : F₃) * form u v :=
    form_mulVec_of_sim (multiplier_spec A)
  have hγm : ∀ s : SL(2, F₃), Am * blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3))
      (((γ s : SL(2, F₃)) : Matrix (Fin 2) (Fin 2) F₃).map σ) * Bm =
      blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3))
        ((γ (diagConj2 (-1) 1 s) : SL(2, F₃)) : Matrix (Fin 2) (Fin 2) F₃) := by
    intro s
    have h := congrArg (mat 3 F₃)
      (rho_chart_sp6 ψ hker τ θ hθ hθτ ρ hρψ γ hγθ s)
    have e : mat 3 F₃ (ρ (longBlock F₃ 3 2 (γ s))) =
        Am * (mat 3 F₃ (longBlock F₃ 3 2 (γ s))).map σ * Bm :=
      mat_conjSp_fieldSp A σ _
    rw [e, mat_longBlock, mat_longBlock, map_blockMat] at h
    exact h
  obtain ⟨hσ, κ, h, hAV, u₂, w₂, hu₂, hw₂, hAu, hAw, huw⟩ :=
    core_three h2 hAB hBA σ hsim hD hsq γ hγm
  obtain ⟨u, w, hfr, hAu', hAw', hu2, hw2⟩ := exists_frame_three h hAV hu₂ hw₂ hAu hAw huw
  obtain ⟨g, hg1, hg2⟩ := exists_g_of_frame hBA h hfr hAu' hAw' (hu2 ▸ hu₂) (hw2 ▸ hw₂)
  have hmapid : ∀ M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F₃, M.map σ = M := fun M => by
    ext i j
    simp [hσ]
  have hfix : ∀ (i j : Fin 3) (hij : i ≠ j) (s : SL(2, F₃)),
      τ (ψ (g * shortBlock F₃ hij s * g⁻¹)) = ψ (g * shortBlock F₃ hij s * g⁻¹) := by
    intro i j hij s
    have hρx : ρ (g * shortBlock F₃ hij s * g⁻¹) = g * shortBlock F₃ hij s * g⁻¹ := by
      apply mat_injective
      have e : mat 3 F₃ (ρ (g * shortBlock F₃ hij s * g⁻¹)) =
          Am * (mat 3 F₃ (g * shortBlock F₃ hij s * g⁻¹)).map σ * Bm :=
        mat_conjSp_fieldSp A σ _
      rw [e, hmapid]
      exact hg2 i j hij s
    rw [← hρψ, hρx]
  refine ⟨g, hg1, ?_, ?_⟩
  · rintro x ⟨_, ⟨s, rfl⟩, rfl⟩
    exact hfix _ _ _ s
  · rintro x ⟨_, ⟨s, rfl⟩, rfl⟩
    exact hfix _ _ _ s

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
end
