public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Qf : QuadraticForm K V}
  (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)

include hnd

theorem eq_of_finrank_movedSpace_mul_le_one {u₁ u₂ : V ≃ₗ[K] V}
    (hu₁ : ∀ v, Qf (u₁ v) = Qf v) (hu₂ : ∀ v, Qf (u₂ v) = Qf v)
    (h₁ : finrank K (movedSpace u₁) = 1) (h₂ : finrank K (movedSpace u₂) = 1)
    (h : finrank K (movedSpace (u₁ * u₂)) ≤ 1) : u₁ = u₂ := by
  obtain ⟨w₁, hQ₁, hspan₁, hform₁⟩ := exists_reflection_form hnd hu₁ h₁
  obtain ⟨w₂, hQ₂, hspan₂, hform₂⟩ := exists_reflection_form hnd hu₂ h₂
  have hw₁ : w₁ ≠ 0 := by
    rintro rfl
    exact hQ₁ (by simp)
  have hw₂ : w₂ ≠ 0 := by
    rintro rfl
    exact hQ₂ (by simp)
  by_cases hli : LinearIndependent K ![w₁, w₂]
  ·
    exfalso
    obtain ⟨x, hx1, hx2⟩ := exists_polar_pair hnd hli (Qf w₁) 0
    obtain ⟨y, hy1, hy2⟩ := exists_polar_pair hnd hli 0 (Qf w₂)
    have hu2x : u₂ x = x := by
      rw [hform₂ x, hx2, zero_div, zero_smul, add_zero]
    have hux : (u₁ * u₂) x = x + w₁ := by
      rw [LinearEquiv.mul_apply, hu2x, hform₁ x, hx1, div_self hQ₁, one_smul]
    have hu2y : u₂ y = y + w₂ := by
      rw [hform₂ y, hy2, div_self hQ₂, one_smul]
    have hu1yw : u₁ (y + w₂) = y + w₂ + (polar Qf w₂ w₁ / Qf w₁) • w₁ := by
      rw [hform₁ (y + w₂), polar_add_left, hy1, zero_add]
    have hyy : (u₁ * u₂) y = y + w₂ + (polar Qf w₂ w₁ / Qf w₁) • w₁ := by
      rw [LinearEquiv.mul_apply, hu2y, hu1yw]
    have hd1 : (u₁ * u₂) x - x = w₁ := by
      rw [hux]
      abel
    have hd2 : (u₁ * u₂) y - y = w₂ + (polar Qf w₂ w₁ / Qf w₁) • w₁ := by
      rw [hyy]
      abel
    have hw1M : w₁ ∈ movedSpace (u₁ * u₂) := by
      rw [← hd1]
      exact sub_mem_movedSpace _ x
    have hw2M' : w₂ + (polar Qf w₂ w₁ / Qf w₁) • w₁ ∈ movedSpace (u₁ * u₂) := by
      rw [← hd2]
      exact sub_mem_movedSpace _ y
    have hw2M : w₂ ∈ movedSpace (u₁ * u₂) := by
      have h' := Submodule.sub_mem _ hw2M' (Submodule.smul_mem _ (polar Qf w₂ w₁ / Qf w₁) hw1M)
      simpa using h'
    have hspanle : Submodule.span K (Set.range ![w₁, w₂]) ≤ movedSpace (u₁ * u₂) := by
      rw [Submodule.span_le, Set.range_subset_iff, Fin.forall_fin_two]
      exact ⟨hw1M, hw2M⟩
    have hfin := Submodule.finrank_mono hspanle
    rw [finrank_span_eq_card hli, Fintype.card_fin] at hfin
    omega
  ·
    have hdep : ∃ c : K, c • w₂ = w₁ := by
      by_contra hcon
      simp only [not_exists] at hcon
      exact hli (linearIndependent_fin2.mpr ⟨hw₂, hcon⟩)
    obtain ⟨c, hc⟩ := hdep
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hw₁ (by rw [← hc, zero_smul])
    subst hc
    refine LinearEquiv.ext fun x => ?_
    rw [hform₁ x, hform₂ x]
    congr 1
    simp only [QuadraticMap.polar_smul_right, QuadraticMap.map_smul, smul_eq_mul, smul_smul]
    congr 1
    field_simp

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
end
