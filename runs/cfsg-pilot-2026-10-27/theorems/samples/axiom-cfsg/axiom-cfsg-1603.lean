public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D α β : Set G}

theorem isTriangle_of_mem_Aalpha (hD : IsOddTransp D) (hN : IsNormalSet D)
    (hblock : IsBlock D α) (hβ : β ∈ Aalpha D α)
    {a b c : G} (ha : a ∈ α) (hc : c ∈ α) (hac : Commute a c) (hane : a ≠ c)
    (hb : b ∈ β) :
    IsTriangle D a b c := by
  classical
  obtain ⟨hclass, hnotperp⟩ := mem_Aalpha_iff.mp hβ
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hclass
  have hbD : b ∈ D := by
    rw [hg] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    exact hN g x (hblock.subset hx)
  have hβD : β ⊆ D := by
    intro y hy
    rw [hg] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hN g x (hblock.subset hx)
  have hβne : β ≠ α := by
    intro h
    exact hnotperp (mem_perp_iff.mpr (Or.inr h))
  have hgene : (fun x => g * x * g⁻¹) '' α ≠ α := by
    rw [← hg]
    exact hβne
  have hbimg : b ∈ (fun x => g * x * g⁻¹) '' α := hg ▸ hb
  have hnotcomm : ∀ x ∈ α, ¬ Commute x b := by
    intro x hx hxb
    have hall : ∀ y ∈ α, ∀ z ∈ (fun x => g * x * g⁻¹) '' α, Commute y z :=
      commute_block_of_mem_apply hN hD hblock hgene hx hbimg hxb
    have hDα : β ∈ Dalpha D α := by
      refine ⟨hclass, hβD, hβne, ?_⟩
      intro y hy z hz
      exact hall y hy z (hg ▸ hz)
    exact hnotperp (mem_perp_iff.mpr (Or.inl hDα))
  exact ⟨hblock.subset ha, hblock.subset hc, hbD, hane, hac,
    hnotcomm a ha, hnotcomm c hc⟩

end CFSG.OddTranspositions
end
