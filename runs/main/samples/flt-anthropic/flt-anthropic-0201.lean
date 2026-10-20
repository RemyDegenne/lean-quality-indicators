namespace P2MW.S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH

set_option autoImplicit false

set_option maxHeartbeats 6400000

open scoped MatrixGroups ModularForm

open UpperHalfPlane CongruenceSubgroup CohCarrier

p2m_reactivate

namespace HeckeGammaH

section Projective

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]

scoped instance : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

variable {M ℓ}

theorem sum_slash_beta_eq_heckeU_add (B : BezoutData M ℓ) (ρ : Gamma0 M) (hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ)
    (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ = f) :
    letI := (GammaHUpper M H ℓ).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ, f ∣[k] beta M H ℓ c) =
      ModularForm.heckeU k ℓ f +
        (f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          ModularForm.heckeDiagMatrix ℓ)) := by
  letI := (GammaHUpper M H ℓ).fintypeQuotientOfFiniteIndex
  rw [← Fintype.sum_bijective _ (bijective_option H B) (fun o => f ∣[k] beta M H ℓ
      (o.elim (QuotientGroup.mk (gammaInf H B)) (fun j => QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))))) _
      (fun _ => rfl), Fintype.sum_option]
  simp only [Option.elim]

  have hterm : ∀ j : Fin ℓ, f ∣[k] beta M H ℓ (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) =
      f ∣[k] ModularForm.heckeMatrix ℓ ((-j : Fin ℓ) : ℕ) := by
    intro j
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (GammaHUpper M H ℓ) (transl M H ((j : ℕ) : ℤ))
    obtain ⟨e, he⟩ := exists_add_neg_eq_mul ℓ j
    have hb : beta M H ℓ (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) =
        (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H ℓ k⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) *
          ModularForm.heckeMatrix ℓ ((-j : Fin ℓ) : ℕ) := by
      simp only [beta]
      rw [hk, Subgroup.coe_mul, mul_inv_rev, map_mul, ← mul_assoc,
        show (((k : ↥(GammaHUpper M H ℓ)) : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ =
          (((k⁻¹ : ↥(GammaHUpper M H ℓ)) : ↥(GammaH M H)) : SL(2, ℤ)) from rfl,
        ← mapGL_conjL_mul_heckeMatrix, mul_assoc, coe_transl,
        heckeMatrix_zero_mul_mapGL_T_zpow_neg ℓ j e he, ← mul_assoc]
    have hmem1 : (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H ℓ k⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
      Subgroup.mem_map_of_mem _ (conjL M H ℓ k⁻¹).2
    have hmem2 : (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) ∈
        (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) := by
      refine Subgroup.mem_map_of_mem _ ?_
      rw [← zpow_neg]
      exact (transl M H (-(e : ℤ))).2
    rw [hb, SlashAction.slash_mul, SlashAction.slash_mul, hf _ hmem1,
      hf _ hmem2]
  simp_rw [hterm]

  have hinf : f ∣[k] beta M H ℓ (QuotientGroup.mk (gammaInf H B)) =
      f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeDiagMatrix ℓ) := by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (GammaHUpper M H ℓ) (gammaInf H B)
    have hb : beta M H ℓ (QuotientGroup.mk (gammaInf H B)) =
        (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H ℓ k⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          ((Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf B : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ) := by
      simp only [beta]
      rw [hk, Subgroup.coe_mul, mul_inv_rev, map_mul, ← mul_assoc,
        show (((k : ↥(GammaHUpper M H ℓ)) : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ =
          (((k⁻¹ : ↥(GammaHUpper M H ℓ)) : ↥(GammaH M H)) : SL(2, ℤ)) from rfl,
        ← mapGL_conjL_mul_heckeMatrix, mul_assoc, heckeMatrix_zero_mul_mapGL_gammaInf_inv]
    have hmem1 : (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H ℓ k⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
      Subgroup.mem_map_of_mem _ (conjL M H ℓ k⁻¹).2

    have hmem3 : (ρ : SL(2, ℤ)) * ((rhoInf B : Gamma0 M) : SL(2, ℤ))⁻¹ ∈ GammaH M H := by
      rw [mem_GammaH_iff]
      refine ⟨(ρ * (rhoInf B)⁻¹).2, ?_⟩
      have e1 : (⟨(ρ : SL(2, ℤ)) * ((rhoInf B : Gamma0 M) : SL(2, ℤ))⁻¹, (ρ * (rhoInf B)⁻¹).2⟩ : Gamma0 M) =
          ρ * (rhoInf B)⁻¹ := rfl
      rw [e1, map_mul, map_inv]
      have hu : gamma0Units M ρ = gamma0Units M (rhoInf B) := by
        ext; rw [val_gamma0Units, val_gamma0Units]
        show ((((ρ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod M) = (((((rhoInf B : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ)) : ZMod M)
        rw [hρ, rhoInf_apply_11, Int.cast_natCast]
      rw [hu, mul_inv_cancel]
      exact one_mem H
    have hmem3' : (Matrix.SpecialLinearGroup.mapGL ℝ ((ρ : SL(2, ℤ)) * ((rhoInf B : Gamma0 M) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ) ∈ (GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
      Subgroup.mem_map_of_mem _ hmem3
    rw [hb, SlashAction.slash_mul, hf _ hmem1]
    conv_rhs => rw [show ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((ρ : SL(2, ℤ)) * ((rhoInf B : Gamma0 M) : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ ((rhoInf B : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ) from by
          rw [← map_mul, inv_mul_cancel_right], mul_assoc, SlashAction.slash_mul,
      hf _ hmem3']
  rw [hinf, add_comm, ModularForm.heckeU_def,
    ← Fin.sum_univ_eq_sum_range (fun i => f ∣[k] ModularForm.heckeMatrix ℓ i) ℓ]
  congr 1
  exact Fintype.sum_equiv (Equiv.neg (Fin ℓ)) _ _ (fun j => rfl)

end Projective
end HeckeGammaH
end P2MW.S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH
