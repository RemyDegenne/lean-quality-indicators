@[expose] public section

namespace BollobasNikiforov

open Matrix Finset Function Filter

open scoped Matrix Topology

variable {k p : ℕ}

noncomputable section

lemma tendsto_MX_extend_submatrix (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (xstar : ℝ) :
    Tendsto (fun ε : ℝ =>
        (M (Xconfig s t (configExtendρ ρ ε)
            (configExtendx x xstar))).submatrix
          configIdxEmbed configIdxEmbed)
      (𝓝[>] 0) (𝓝 (M (Xconfig s t ρ x))) := by
  refine tendsto_pi_nhds.2 fun α => tendsto_pi_nhds.2 fun β => ?_
  rcases eq_or_ne α β with rfl | hne
  · set c := configVec s t ρ x α 0 * xstar + configVec s t ρ x α 1
    have hform :
        Tendsto (fun ε : ℝ =>
            M (Xconfig s t ρ x) α α +
              if c < 0 then ε * c ^ 2 else 0)
          (𝓝[>] 0) (𝓝 (M (Xconfig s t ρ x) α α)) := by
      by_cases hc : c < 0
      · simp only [hc, ite_true]
        have hlim :
            Tendsto (fun ε : ℝ => M (Xconfig s t ρ x) α α + ε * c ^ 2)
              (𝓝[>] 0) (𝓝 (M (Xconfig s t ρ x) α α + 0 * c ^ 2)) :=
          tendsto_const_nhds.add
            ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul
              tendsto_const_nhds)
        simpa using hlim
      · simp only [hc, ite_false, add_zero]
        exact tendsto_const_nhds
    have heq :
        (fun ε : ℝ =>
          (M (Xconfig s t (configExtendρ ρ ε)
              (configExtendx x xstar))).submatrix configIdxEmbed
              configIdxEmbed α α) =ᶠ[𝓝[>] (0 : ℝ)]
          fun ε => M (Xconfig s t ρ x) α α +
            if c < 0 then ε * c ^ 2 else 0 :=
      eventually_of_mem self_mem_nhdsWithin fun ε hε => by
        have hε' : 0 < ε := hε
        simp [submatrix_apply, MX_extend_submatrix_diag s t ρ x hε' xstar α, c]
    exact hform.congr' heq.symm
  · refine tendsto_const_nhds.congr fun ε => ?_
    simp [submatrix_apply, MX_extend_submatrix_of_ne s t ρ x ε xstar hne]

end
end BollobasNikiforov
end
