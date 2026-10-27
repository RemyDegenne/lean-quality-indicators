public section

namespace CFSG.ClassicalInvolution.NDB.SpinStd

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
  CFSG.ClassicalInvolution.Asc77 CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.NDB.FourFrame CFSG.ClassicalInvolution.NDB.ExoticModel QuadraticMap

open scoped MatrixGroups

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {m : ℕ}

omit [Finite F] [FiniteDimensional F V] in
theorem exists_frames (h2 : (2 : F) ≠ 0) (F₀ : HypFrame Q m) {i₀ i₁ i₂ : Fin m} (h01 : i₀ ≠ i₁)
    (h12 : i₁ ≠ i₂) (h02 : i₀ ≠ i₂) {θ : SL(3, F) →* spinGroup Q}
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) {c : SL(3, F)}
    (hpair : (((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ =
          (F₀.longSL2 h01 true false).range ∧
        ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ = (F₀.longSL2 h12 true false).range) ∨
      (((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ = (F₀.longSL2 h12 true false).range ∧
        ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ =
          (F₀.longSL2 h01 true false).range)) :
    ∃ frX frY : Frame Q, spinAction Q (θ (c⁻¹ * SL3.u₁ * c)) = frX.La (-1) ∧
      spinAction Q (θ (c⁻¹ * SL3.u₂ * c)) = frY.La (-1) ∧
      (∃ P : HypPair Q, P.e ∈ frX.span ∧ P.e ∈ frY.span ∧ P.f ∈ frX.span ∧ P.f ∈ frY.span) ∧
      ∃ u ∈ frX.span, u ∈ frY.perp ∧ Q u ≠ 0 := by
  have hrel := frameRel_sl3 h2 θ hker c
  have hκy := thetaC_π_u₁ θ c
  have hy₁m : θ (c⁻¹ * SL3.u₁ * c) ∈ ((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ :=
    Subgroup.mem_map_of_mem θ (SL3.conj_mem c)
  have hy₂m : θ (c⁻¹ * SL3.u₂ * c) ∈ ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ :=
    Subgroup.mem_map_of_mem θ ⟨SL3.u₂, SL3.u₂_mem, by simp⟩
  have hy₂sq : θ (c⁻¹ * SL3.u₂ * c) * θ (c⁻¹ * SL3.u₂ * c) = 1 := by
    rw [← hκy]
    calc θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.u₁ * c) * (θ (c⁻¹ * SL3.π * c))⁻¹ *
          (θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.u₁ * c) * (θ (c⁻¹ * SL3.π * c))⁻¹) =
        θ (c⁻¹ * SL3.π * c) * (θ (c⁻¹ * SL3.u₁ * c) * θ (c⁻¹ * SL3.u₁ * c)) *
          (θ (c⁻¹ * SL3.π * c))⁻¹ := by group
      _ = 1 := by rw [hrel.sq]; group
  have hy₂1 : θ (c⁻¹ * SL3.u₂ * c) ≠ 1 := by
    rw [← hκy]
    intro h
    apply hrel.ne_one
    calc θ (c⁻¹ * SL3.u₁ * c) = (θ (c⁻¹ * SL3.π * c))⁻¹ *
          (θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.u₁ * c) * (θ (c⁻¹ * SL3.π * c))⁻¹) *
          θ (c⁻¹ * SL3.π * c) := by group
      _ = 1 := by rw [h]; group
  have hP₀ : (vecPair F₀ i₁).e ∈ (F₀.toFrame h01 true false).span ∧
      (vecPair F₀ i₁).e ∈ (F₀.toFrame h12 true false).span ∧
      (vecPair F₀ i₁).f ∈ (F₀.toFrame h01 true false).span ∧
      (vecPair F₀ i₁).f ∈ (F₀.toFrame h12 true false).span :=
    ⟨vec_mem_span_snd F₀ h01 true, vec_mem_span_fst F₀ h12 true, vec_mem_span_snd F₀ h01 false,
      vec_mem_span_fst F₀ h12 false⟩
  have hne : (1 : F) ≠ 0 := one_ne_zero
  rcases hpair with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · refine ⟨F₀.toFrame h01 true false, F₀.toFrame h12 true false, ?_, ?_,
      ⟨vecPair F₀ i₁, hP₀⟩, F₀.vec i₀ true + F₀.vec i₀ false,
      add_mem (vec_mem_span_fst F₀ h01 true) (vec_mem_span_fst F₀ h01 false),
      add_mem (vec_mem_perp F₀ h12 h01 h02 true) (vec_mem_perp F₀ h12 h01 h02 false),
      by rw [map_vec_add]; exact hne⟩
    · rw [eq_longSL2_neg_one F₀ h2 h01 (hA ▸ hy₁m) hrel.sq hrel.ne_one,
        spinAction_longSL2_neg_one]
    · rw [eq_longSL2_neg_one F₀ h2 h12 (hB ▸ hy₂m) hy₂sq hy₂1, spinAction_longSL2_neg_one]
  · refine ⟨F₀.toFrame h12 true false, F₀.toFrame h01 true false, ?_, ?_,
      ⟨vecPair F₀ i₁, hP₀.2.1, hP₀.1, hP₀.2.2.2, hP₀.2.2.1⟩, F₀.vec i₂ true + F₀.vec i₂ false,
      add_mem (vec_mem_span_snd F₀ h12 true) (vec_mem_span_snd F₀ h12 false),
      add_mem (vec_mem_perp F₀ h01 h02.symm h12.symm true)
        (vec_mem_perp F₀ h01 h02.symm h12.symm false),
      by rw [map_vec_add]; exact hne⟩
    · rw [eq_longSL2_neg_one F₀ h2 h12 (hA ▸ hy₁m) hrel.sq hrel.ne_one,
        spinAction_longSL2_neg_one]
    · rw [eq_longSL2_neg_one F₀ h2 h01 (hB ▸ hy₂m) hy₂sq hy₂1, spinAction_longSL2_neg_one]

end CFSG.ClassicalInvolution.NDB.SpinStd
end
