public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride

open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35

section Main

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem Data.exists_le_Ws
    {h : Counterexample p A θ} {E B V : Subgroup G} {r : ℕ}
    {Y : Fin p → Subgroup G} (D : Data h E) (hS : Setting p A E B) (hV : VData p A θ E V r)
    (hY : Decomp p A θ E B Y) {b : G} (hb : b ∈ B) (hbE : b ∉ E) {L : Subgroup G}
    (hL : L ∈ lcal (θ b)) : ∃ i, L ≤ Ws V Y i := by
  have hbA := hS.mem_A hb
  have hdp := D.isDirectProduct_lcal hbA hbE
  obtain ⟨e, he⟩ := hY.comp b hb hbE
  refine ⟨e ⟨L, hL⟩, (D.le_inf_sup_Ff hS hV hb hbE hL).trans ?_⟩
  have hFf : Ff p A θ E L = Y (e ⟨L, hL⟩) := he ⟨L, hL⟩
  have hVL : V ⊓ L ≤ Vs V Y (e ⟨L, hL⟩) := by
    intro x hx
    refine mem_Vs_iff.mpr ⟨hx.1, fun k hk y hy => ?_⟩
    have hY' : Y k = Ff p A θ E (e.symm k) := by rw [he (e.symm k), Equiv.apply_symm_apply]
    have hLL' : ((e.symm k : ↥(lcal (θ b))) : Subgroup G) ≠ L := fun heq => hk (by
      have : e.symm k = ⟨L, hL⟩ := Subtype.ext heq
      rw [← this, Equiv.apply_symm_apply])
    have hyL : y ∈ ((e.symm k : ↥(lcal (θ b))) : Subgroup G) :=
      Ff_le_left E _ (hY' ▸ hy)
    exact (hdp.commute L hL _ (e.symm k).2 (Ne.symm hLL') x hx.2 y hyL).eq.symm
  unfold Ws
  rw [hFf, sup_comm]
  exact sup_le_sup_left hVL _

end Main
end CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35
end
