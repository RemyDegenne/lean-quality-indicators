public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T T₁ : Subgroup G}

namespace Cfg56

variable (c : Cfg56 T T₁)

include c

theorem conj_comm_cases {a e x : G} (ha : a ∈ secA T T₁) (ha1 : a ≠ 1) (hex : x * a * x⁻¹ = e)
    (hcomm : e * a = a * e) :
    e ∈ secA T T₁ ∨ (IsUIdx T T₁ x ∧ e ∈ conjSubgroup x (secA T T₁)) := by
  have := c.hy.finite
  have hN : e ∈ Subgroup.normalizer (T : Set G) :=
    c.hy.pair.wc.centralizer_le_normalizer (secA_le_left ha) ha1
      (Subgroup.mem_centralizer_singleton_iff.2 hcomm)
  have heA' : e ∈ conjSubgroup x (secA T T₁) := by
    rw [← hex]
    exact conj_mem_conjSubgroup x ha
  by_cases hxT : conjSubgroup x T = T
  · left
    have hxN : x ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_iff_conjSubgroup_eq.2 hxT
    rwa [conjSubgroup_secA hxN] at heA'
  · right
    have he1 : e ≠ 1 := by
      rintro rfl
      apply ha1
      have : a = x⁻¹ * (x * a * x⁻¹) * x := by group
      rw [this, hex]
      group
    have heT' : e ∈ conjSubgroup x T := by
      rw [← hex]
      exact conj_mem_conjSubgroup x (secA_le_left ha)
    have hL : normIn (conjSubgroup x T) T ≠ ⊥ := by
      intro hbot
      have hmem : e ∈ normIn (conjSubgroup x T) T := mem_normIn.2 ⟨heT', hN⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact he1 hmem
    have hle := conjSubgroup_secA_le_normIn c.hy.pair c.hS hxT hL
    exact ⟨c.hplus x (fun y hy => (mem_normIn.1 (hle hy)).2) hxT, heA'⟩

end Cfg56
end CFSG.CGT.T75O
end
