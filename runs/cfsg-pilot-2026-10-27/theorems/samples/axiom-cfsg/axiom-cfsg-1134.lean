public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

open CFSG.Quasithin.H13 CFSG.KGroups.Sp6 CFSG.Quasithin.G2U CFSG.Open

theorem pcore_N0_le
    (W : Subgroup H6) (hWN : W ≤ N0) (hW : N0 ≤ Subgroup.normalizer (W : Set H6))
    (hp : IsPGroup 3 W) : W ≤ B0 := by
  have h81 := pow_81_of_isPGroup W hWN hp
  intro x hx
  obtain ⟨t, ht, hrep, hgt⟩ := exists_rep_genB_N0 (hWN hx)
  by_cases hB : inTab (tabOf gensB 27) t = true
  · exact mem_Hgen_of_rep tabCheck_B (inTab_iff.1 hB) hrep
  · exfalso
    have h3 := N0_spec.2.2.2.1
    simp only [propN3] at h3
    have h := forall_of_allCheck h3 t ht
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Array.any_eq_true'] at h
    rcases h with (h | h) | ⟨n, hn, h⟩
    · exact hB h
    · exact h ((hrep.pow 81).eq_one_iff.1 (h81 x hx))
    · obtain ⟨n', hn'N, hnrep, hgn⟩ := exists_mem_N0_of_mem_tab hn
      have hc : x * (n' * (x⁻¹ * n'⁻¹)) ∈ W := by
        refine mul_mem hx ?_
        have := (Subgroup.mem_normalizer_iff.1 (hW hn'N) x⁻¹).1 (inv_mem hx)
        simpa [mul_assoc] using this
      have hrc := hrep.commutator hgt hnrep hgn
      exact h (((hrc.pow 81).eq_one_iff).1 (h81 _ hc))

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
end
