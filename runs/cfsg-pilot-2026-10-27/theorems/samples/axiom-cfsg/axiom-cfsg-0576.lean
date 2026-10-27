public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

open Fin.NatCast

variable {G : Type*} [Group G] {x₁ x₂ lam : G}

theorem WreathRel.exists_embedding (h : WreathRel x₁ x₂ lam) :
    ∃ φ : WMod →* G, Function.Injective φ ∧ φ.range = wreathGrp x₁ x₂ lam ∧
      φ WMod.wx₁ = x₁ ∧ φ WMod.wx₂ = x₂ ∧ φ WMod.wlam = lam := by
  refine ⟨embHom h, ?hinj, ?hrange, ?hx₁, ?hx₂, ?hlam⟩
  · intro g g' heq
    obtain ⟨a, b, i⟩ := g
    obtain ⟨a', b', i'⟩ := g'
    change x₁ ^ a.val * x₂ ^ b.val * lam ^ i.val =
      x₁ ^ a'.val * x₂ ^ b'.val * lam ^ i'.val at heq
    fin_cases i <;> fin_cases i'
    · simp only [Fin.val_zero, pow_zero, mul_one] at heq
      obtain ⟨haa, hbb⟩ := base_inj h heq
      simp [haa, hbb]
    · simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one] at heq
      exfalso
      have hmem : lam ∈ baseGrp x₁ x₂ := by
        have h2 : (x₁ ^ a'.val * x₂ ^ b'.val)⁻¹ * (x₁ ^ a.val * x₂ ^ b.val) = lam := by
          rw [heq]; group
        rw [← h2]
        exact mul_mem
          (inv_mem (mul_mem (pow_mem (subset_closure (by simp)) a'.val)
            (pow_mem (subset_closure (by simp)) b'.val)))
          (mul_mem (pow_mem (subset_closure (by simp)) a.val)
            (pow_mem (subset_closure (by simp)) b.val))
      exact lam_notMem_base h hmem
    · simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one] at heq
      exfalso
      have hmem : lam ∈ baseGrp x₁ x₂ := by
        have h2 : (x₁ ^ a.val * x₂ ^ b.val)⁻¹ * (x₁ ^ a'.val * x₂ ^ b'.val) = lam := by
          rw [← heq]; group
        rw [← h2]
        exact mul_mem
          (inv_mem (mul_mem (pow_mem (subset_closure (by simp)) a.val)
            (pow_mem (subset_closure (by simp)) b.val)))
          (mul_mem (pow_mem (subset_closure (by simp)) a'.val)
            (pow_mem (subset_closure (by simp)) b'.val))
      exact lam_notMem_base h hmem
    · simp only [Fin.val_one, pow_one] at heq
      obtain ⟨haa, hbb⟩ := base_inj h (mul_right_cancel heq)
      simp [haa, hbb]
  · apply le_antisymm
    · rintro y ⟨g, rfl⟩
      obtain ⟨a, b, i⟩ := g
      change x₁ ^ a.val * x₂ ^ b.val * lam ^ i.val ∈ wreathGrp x₁ x₂ lam
      rw [wreathGrp]
      exact mul_mem
        (mul_mem (pow_mem (subset_closure (by simp)) a.val)
          (pow_mem (subset_closure (by simp)) b.val))
        (pow_mem (subset_closure (by simp)) i.val)
    · rw [wreathGrp, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨WMod.wx₁, by simp [embHom, WMod.wx₁]⟩
      · exact ⟨WMod.wx₂, by simp [embHom, WMod.wx₂]⟩
      · exact ⟨WMod.wlam, by simp [embHom, WMod.wlam]⟩
  · simp [embHom, WMod.wx₁]
  · simp [embHom, WMod.wx₂]
  · simp [embHom, WMod.wlam]

end CFSG.OddStandard.SmallF3.HarrisU33
end
