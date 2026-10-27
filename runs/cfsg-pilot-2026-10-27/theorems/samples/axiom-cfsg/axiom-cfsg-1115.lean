public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {M C : Subgroup V}

theorem fix_B1_le_C (D : L3Data G M C) (hCfix : ∀ g ∈ G, ∀ c ∈ C, g c = c) {m : V} (hm : IsLift D m)
    (hII : ∃ s : L3.Γ, L3F.Ustd s ∧ D.rho s m ≠ m) :
    ∀ x ∈ M, (∀ b ∈ L3F.B1, D.rho b x = x) → x ∈ C := by
  intro x hxM hxB1
  obtain ⟨s, hsU, hsm⟩ := hII
  by_contra hxC
  have hβne : D.β ⟨x, hxM⟩ ≠ 1 := fun h => hxC ((D.ker_β ⟨x, hxM⟩).1 h)
  have hv0 : Multiplicative.toAdd (D.β ⟨x, hxM⟩) ≠ 0 := fun h => hβne (toAdd_eq_zero.mp h)
  have hvB1 : ∀ b ∈ L3F.B1,
      L3.act b (Multiplicative.toAdd (D.β ⟨x, hxM⟩)) = Multiplicative.toAdd (D.β ⟨x, hxM⟩) :=
    fun b hb => beta_fixed_act D hxM (hxB1 b hb)
  obtain ⟨p, hp, hpv⟩ := L3F.Pline_trans _ (L3F.B1_fix _ hvB1) hv0
  have hyM : D.rho p x ∈ M := D.inv_U _ (D.rho_mem p) x hxM
  have hyβ : D.β ⟨D.rho p x, hyM⟩ = Multiplicative.ofAdd L3F.e1 := by
    rw [D.β_rho p x hxM hyM, hpv]
  have hyB1 : ∀ b ∈ L3F.B1, D.rho b (D.rho p x) = D.rho p x := by
    intro b hb
    obtain ⟨b', hb', hbb'⟩ := L3F.Pline_norm p hp b hb
    rw [← rho_mul_apply_L3, hbb', rho_mul_apply_L3, hxB1 b' hb']
  obtain ⟨hmM, hβm⟩ := lift_spec hm
  have hcm : D.rho p x * m⁻¹ ∈ C := beta_eq_mem_C D hyM hmM (hyβ.trans hβm.symm)
  obtain ⟨c, hc, hcy⟩ : ∃ c ∈ C, D.rho p x = c * m := ⟨D.rho p x * m⁻¹, hcm, by simp⟩
  have hB1m : ∀ b ∈ L3F.B1, D.rho b m = m := by
    intro b hb
    have e := hyB1 b hb
    rw [hcy, map_mul, hCfix (D.rho b) (D.rho_mem b) c hc] at e
    exact mul_left_cancel e
  obtain ⟨b₁, hb₁, b₂, hb₂, hsb⟩ := U_B1B2_decomp s hsU
  apply hsm
  rw [hsb, rho_mul_apply_L3, lift_B2 D hCfix hm hb₂, hB1m b₁ hb₁]

end CFSG.Quasithin.C116Three
end
