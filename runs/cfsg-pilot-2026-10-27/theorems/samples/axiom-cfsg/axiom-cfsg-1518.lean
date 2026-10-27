public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

open scoped commutatorElement

variable {G : Type} [Group G] {t : G} {i₁ i₂ : SL5 →* G}

theorem WongHyp.commutator_eq_of_commute_x (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {k k' : G}
    (hk : k ∈ i₁.range ⊔ i₂.range) (hk' : k' ∈ i₁.range ⊔ i₂.range)
    (hkx : Commute k (i₁ hM * i₂ hM)) (hk'x : Commute k' (i₁ hM * i₂ hM)) :
    ⁅k, k'⁆ = 1 ∨ ⁅k, k'⁆ = t := by
  have hcommSL : ∀ x y : SL5, Commute (i₁ x) (i₂ y) :=
    fun x y => h.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have hprod : ∀ x y x' y' : SL5,
      (i₁ x * i₂ y) * (i₁ x' * i₂ y') = i₁ (x * x') * i₂ (y * y') := by
    intro x y x' y'
    rw [map_mul, map_mul, mul_assoc, ← mul_assoc (i₂ y), ← (hcommSL x' y).eq,
      mul_assoc (i₁ x'), ← mul_assoc]
  have hchar : ∀ x y : SL5, Commute (i₁ x * i₂ y) (i₁ hM * i₂ hM) ↔
      (hM * x = x * hM ∧ hM * y = y * hM) ∨
        (hM * x = -(x * hM) ∧ hM * y = -(y * hM)) := by
    intro x y
    rw [commute_iff_eq, hprod x y hM hM, hprod hM hM x y,
      prodHom_eq_iff hi₁ hi₂ h.orderOf_t hcommSL h.inf_eq]
  have hc1 : cM⁻¹ = -cM :=
    inv_eq_of_mul_eq_one_right (by rw [mul_neg, ← pow_two, cM_sq, neg_neg])
  have hc2 : (-cM)⁻¹ = cM :=
    inv_eq_of_mul_eq_one_right (by rw [neg_mul, ← pow_two, cM_sq, neg_neg])
  have hc3 : (hM * cM)⁻¹ = -(hM * cM) :=
    inv_eq_of_mul_eq_one_right (by rw [mul_neg, ← pow_two, hM_mul_cM_sq, neg_neg])
  have hc4 : (-(hM * cM))⁻¹ = hM * cM :=
    inv_eq_of_mul_eq_one_right (by rw [neg_mul, ← pow_two, hM_mul_cM_sq, neg_neg])
  have hcomm_hM : ∀ x : SL5, hM * x = x * hM → x = 1 ∨ x = -1 ∨ x = hM ∨ x = -hM := by
    intro x hx
    have hc : Commute x hM := by rw [commute_iff_eq]; exact hx.symm
    exact (commute_hM_iff x).mp hc
  have hcomm_inv : ∀ x : SL5, hM * x = -(x * hM) →
      x = cM ∨ x = -cM ∨ x = hM * cM ∨ x = -(hM * cM) := by
    intro x hx
    have hx' : hM * x = x * hM⁻¹ := by rw [hx, ← mul_neg, neg_hM]
    have h1 : x⁻¹ * hM * x = hM⁻¹ := by
      calc x⁻¹ * hM * x = x⁻¹ * (hM * x) := by group
        _ = x⁻¹ * (x * hM⁻¹) := by rw [hx']
        _ = hM⁻¹ := by group
    rcases (conj_hM_eq_inv_iff x⁻¹).mp (by simpa using h1) with h1 | h1 | h1 | h1
    · right; left; rw [← inv_inv x, h1, hc1]
    · left; rw [← inv_inv x, h1, hc2]
    · right; right; right; rw [← inv_inv x, h1, hc3]
    · right; right; left; rw [← inv_inv x, h1, hc4]
  have hQ8comm : ∀ x y : SL5,
      x ∈ ({1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)} : Set SL5) →
      y ∈ ({1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)} : Set SL5) →
      ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = -1 := by
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  obtain ⟨g, g', hk_eq⟩ := (mem_sup_iff hcommSL).mp hk
  obtain ⟨f, f', hk'_eq⟩ := (mem_sup_iff hcommSL).mp hk'
  have hkx' : Commute (i₁ g * i₂ g') (i₁ hM * i₂ hM) := by rw [hk_eq]; exact hkx
  have hk'x' : Commute (i₁ f * i₂ f') (i₁ hM * i₂ hM) := by rw [hk'_eq]; exact hk'x
  have hgQ : g ∈ ({1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)} : Set SL5) := by
    rcases (hchar g g').mp hkx' with ⟨h1, -⟩ | ⟨h1, -⟩
    · rcases hcomm_hM g h1 with hh | hh | hh | hh <;> simp [hh]
    · rcases hcomm_inv g h1 with hh | hh | hh | hh <;> simp [hh]
  have hg'Q : g' ∈ ({1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)} : Set SL5) := by
    rcases (hchar g g').mp hkx' with ⟨-, h1⟩ | ⟨-, h1⟩
    · rcases hcomm_hM g' h1 with hh | hh | hh | hh <;> simp [hh]
    · rcases hcomm_inv g' h1 with hh | hh | hh | hh <;> simp [hh]
  have hfQ : f ∈ ({1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)} : Set SL5) := by
    rcases (hchar f f').mp hk'x' with ⟨h1, -⟩ | ⟨h1, -⟩
    · rcases hcomm_hM f h1 with hh | hh | hh | hh <;> simp [hh]
    · rcases hcomm_inv f h1 with hh | hh | hh | hh <;> simp [hh]
  have hf'Q : f' ∈ ({1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)} : Set SL5) := by
    rcases (hchar f f').mp hk'x' with ⟨-, h1⟩ | ⟨-, h1⟩
    · rcases hcomm_hM f' h1 with hh | hh | hh | hh <;> simp [hh]
    · rcases hcomm_inv f' h1 with hh | hh | hh | hh <;> simp [hh]
  have hgf : ⁅g, f⁆ = 1 ∨ ⁅g, f⁆ = -1 := hQ8comm g f hgQ hfQ
  have hg'f' : ⁅g', f'⁆ = 1 ∨ ⁅g', f'⁆ = -1 := hQ8comm g' f' hg'Q hf'Q
  have hfactor : ⁅k, k'⁆ = i₁ ⁅g, f⁆ * i₂ ⁅g', f'⁆ := by
    rw [show k = i₁ g * i₂ g' from hk_eq.symm, show k' = i₁ f * i₂ f' from hk'_eq.symm]
    rw [show i₁ g * i₂ g' = prodHom hcommSL (g, g') from rfl,
      show i₁ f * i₂ f' = prodHom hcommSL (f, f') from rfl]
    rw [← map_commutatorElement (prodHom hcommSL) (g, g') (f, f'), prodHom_apply]
    rfl
  have hmem : ∀ e : SL5, e = 1 ∨ e = -1 → i₁ e = 1 ∨ i₁ e = t := by
    rintro e (rfl | rfl)
    · left; rw [map_one]
    · right; rw [← eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq]
  have hmem' : ∀ e : SL5, e = 1 ∨ e = -1 → i₂ e = 1 ∨ i₂ e = t := by
    rintro e (rfl | rfl)
    · left; rw [map_one]
    · right; rw [← eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq]
  have ht2 : t * t = 1 := by rw [← pow_two, ← h.orderOf_t, pow_orderOf_eq_one]
  rw [hfactor]
  rcases hmem _ hgf with h1 | h1 <;> rcases hmem' _ hg'f' with h2 | h2 <;> rw [h1, h2]
  · left; rw [one_mul]
  · right; rw [one_mul]
  · right; rw [mul_one]
  · left; rw [ht2]

end CFSG.OddTranspositions.PartThree.Wong
end
