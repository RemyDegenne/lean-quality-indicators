public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem gram3_eq_four
    {α β γ : Fin τ.rank → ℤ} (hα : iform α α = 2) (hβ : iform β β = 2)
    (hγ : iform γ γ = 2) (hne1 : β ≠ α) (hne2 : β ≠ -α) (hs : iform α β ≠ 0)
    (hbc : iform α γ ≠ 0 ∨ iform β γ ≠ 0) (hg : gramDet3 α β γ ≠ 0) : gramDet3 α β γ = 4 := by
  obtain ⟨hdep1, hdep2, hdep3, hdep4⟩ := gram3_dependent hα hβ
  have hγ1 : γ ≠ α := fun h => hg (h ▸ hdep1)
  have hγ2 : γ ≠ -α := fun h => hg (h ▸ hdep2)
  have hγ3 : γ ≠ β := fun h => hg (h ▸ hdep3)
  have hγ4 : γ ≠ -β := fun h => hg (h ▸ hdep4)
  obtain ⟨ha1, ha2⟩ := abs_iform_le_one hα hβ hne1 hne2
  obtain ⟨hb1, hb2⟩ := abs_iform_le_one hα hγ hγ1 hγ2
  obtain ⟨hc1, hc2⟩ := abs_iform_le_one hβ hγ hγ3 hγ4
  have key : ∀ a b c : ℤ, -1 ≤ a → a ≤ 1 → a ≠ 0 → -1 ≤ b → b ≤ 1 → -1 ≤ c → c ≤ 1 →
      (b ≠ 0 ∨ c ≠ 0) → 8 + 2 * (a * b * c) - 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≠ 0 →
      8 + 2 * (a * b * c) - 2 * (a ^ 2 + b ^ 2 + c ^ 2) = 4 := by
    intro a b c h1 h2 h3 h4 h5 h6 h7 h8 h9
    interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all
  exact key _ _ _ ha1 ha2 hs hb1 hb2 hc1 hc2 hbc hg

end CFSG.StandardType.TableCRes
end
