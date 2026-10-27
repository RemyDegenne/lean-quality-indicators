public section

namespace CFSG.Quasithin.H13.Ch9.TN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem three_inner_of_quot {X M : Type} [Group X] [Group M] (hX : Group.IsPerfect X)
    (e : X ⧸ Subgroup.center X ≃* M)
    (hM : ∀ β : MulAut M, Odd (orderOf β) → ∃ x : M, β = MulAut.conj x) :
    ∀ α : MulAut X, α ^ 3 = 1 → ∃ x : X, α = MulAut.conj x := by
  intro α hα
  set β : MulAut M := MulAut.congr e (NQCat.T513P.descZ X α) with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, ← map_pow, hα, map_one, map_one]
  have hβo : Odd (orderOf β) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hβ3)
  obtain ⟨m, hm⟩ := hM β hβo
  have hmem : NQCat.T513P.descZ X α ∈ inner (X ⧸ Subgroup.center X) := by
    refine ⟨e.symm m, ?_⟩
    apply MulEquiv.ext
    intro y
    have h1 := congrArg (fun γ : MulAut M => γ (e y)) hm
    simp only [hβ, MulAut.congr_apply, MulAut.conj_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h1
    apply e.injective
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h1.symm
  obtain ⟨x, hx⟩ := NQCat.T513P.mem_inner_of_descZ_mem_inner hX hmem
  exact ⟨x, hx.symm⟩

end CFSG.Quasithin.H13.Ch9.TN
end
