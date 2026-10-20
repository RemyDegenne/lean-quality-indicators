@[expose] public section

open Module (finrank)

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

theorem eigenvalues_eq_of_eigenbasis
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) (w : OrthonormalBasis (Fin n) 𝕜 E)
    {μ : Fin n → ℝ} (hμ : Antitone μ) (hw : ∀ i, S (w i) = (μ i : 𝕜) • w i) :
    hS.eigenvalues hn = μ := by
  funext k
  refine le_antisymm ?_ ?_
  · -- `λₖ ≤ μₖ`: intersect the CF-lower witness with the `w`-tail span.
    obtain ⟨V, hVdim, hVlow⟩ :=
      hS.exists_submodule_forall_unit_eigenvalue_le_re_inner hn k
    set W := w.spanIndices ↑(Finset.Ici k) with hW
    have hWdim : finrank 𝕜 W = n - (k : ℕ) := by
      rw [hW, w.finrank_spanIndices, Fin.card_Ici]
    have hinf : V ⊓ W ≠ ⊥ :=
      inf_ne_bot_of_finrank_lt (by have hk : (k : ℕ) < n := k.2; omega)
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
    obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
    have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
    set x := ((‖z‖⁻¹ : ℝ) : 𝕜) • z with hx
    have hnx : ‖x‖ = 1 := by
      rw [hx, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
    have hxW : x ∈ W := W.smul_mem _ hzW
    calc hS.eigenvalues hn k ≤ RCLike.re ⟪S x, x⟫_𝕜 := hVlow x (V.smul_mem _ hzV) hnx
      _ ≤ μ k * ‖x‖ ^ 2 :=
          re_inner_le_of_eigenbasis hS w hw (fun _ hik => hμ (by simpa using hik)) hxW
      _ = μ k := by rw [hnx]; ring
  · -- `μₖ ≤ λₖ`: test the CF-upper bound on the `w`-head span.
    set V := w.spanIndices ↑(Finset.Iic k) with hV
    have hVdim : finrank 𝕜 V = (k : ℕ) + 1 := by
      rw [hV, w.finrank_spanIndices, Fin.card_Iic]
    obtain ⟨x, hxV, hnx, hup⟩ :=
      hS.exists_unit_vector_re_inner_le_eigenvalue hn k V hVdim
    calc μ k = μ k * ‖x‖ ^ 2 := by rw [hnx]; ring
      _ ≤ RCLike.re ⟪S x, x⟫_𝕜 :=
          le_re_inner_of_eigenbasis hS w hw (fun _ hik => hμ (by simpa using hik)) hxV
      _ ≤ hS.eigenvalues hn k := hup

end LinearMap.IsSymmetric
end
