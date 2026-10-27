public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}

theorem g10_4 (h3 : G1003Stmt) (hB49 : B49Stmt) : G1004Stmt := by
  intro V _ _ _ B Γ v₁ W X X₀ hyp H hHΓ hHn hH1 U hU0 hU1 hirr hcase
  have hUK : Invariant (H ⊔ X) U := hirr.1
  have hUH : Invariant H U := fun h hh u hu => hUK h (Subgroup.mem_sup_left hh) u hu
  have hUX : Invariant X U := fun x hx u hu => hUK x (Subgroup.mem_sup_right hx) u hu
  obtain ⟨h1, h2⟩ : v₁ ∉ U ∧ ∃ u ∈ U, B v₁ u ≠ 0 := by
    rcases hcase with hHG | ⟨h1, hc⟩
    · have hUΓ : Invariant Γ U := by
        rw [← hHG]
        exact hUH
      exact ⟨hyp.notMem_of_invariant hUΓ hU1, hyp.exists_not_perp_of_invariant hUΓ hU0⟩
    · exact ⟨h1, hyp.exists_not_perp_of_comm hUX h1 hc⟩
  obtain ⟨hWU, -, -, -, -⟩ := hyp.counting U hUX h1 h2
  have hW1 : 1 ≤ Module.finrank (ZMod 2) W := by
    apply Nat.succ_le_of_lt
    apply Module.finrank_pos_iff_exists_ne_zero.2
    exact ⟨⟨v₁, hyp.mem_W⟩, fun h => hyp.point (congrArg Subtype.val h)⟩
  have hn1 : 1 ≤ Module.finrank (ZMod 2) U := by
    apply Nat.succ_le_of_lt
    apply Module.finrank_pos_iff_exists_ne_zero.2
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    exact ⟨⟨u, hu⟩, fun h => hu0 (congrArg Subtype.val h)⟩
  have hWle := hyp.finrank_isotropic_le
  obtain ⟨r, hr⟩ : Even (Module.finrank (ZMod 2) V) :=
    LinearMap.BilinForm.IsAlt.even_finrank (K := ZMod 2) (fun v => hyp.alt v) hyp.nondegenerate'
  have hcases : Module.finrank (ZMod 2) U = 1 ∨ Module.finrank (ZMod 2) U = 2 ∨
      3 ≤ Module.finrank (ZMod 2) U := by omega
  rcases hcases with hn | hn | hn
  · exfalso
    rcases hcase with hHG | ⟨-, hc⟩
    · have hUΓ : Invariant Γ U := by
        rw [← hHG]
        exact hUH
      exact g10Four_n_one_case_one hyp hUΓ h1 h2 hn (by omega)
    · exact hc (g10Four_n_one_case_two hyp hUX h1 h2 hn)
  · have hd4 : Module.finrank (ZMod 2) V = 4 := by omega
    refine ⟨hd4, hn, ?_⟩
    rcases hcase with hHG | ⟨-, -⟩
    · have hUΓ : Invariant Γ U := by
        rw [← hHG]
        exact hUH
      exact isSolvable_of_invariant_subspace_four B hyp.alt hyp.nondegenerate hd4 Γ
        (fun γ hγ v w => hyp.isometry γ hγ v w) U hUΓ hU0 hU1
    · exact isSolvable_of_normal_invariant_two B hyp.alt hyp.nondegenerate hd4 Γ H
        (fun γ hγ v w => hyp.isometry γ hγ v w) hHΓ hHn hH1 U hn hUH
  · exact (g10Four_big h3 hB49 hyp hHΓ hHn hirr h1 h2 hn).elim

end CFSG.Quasithin
end
