namespace OAI

noncomputable section

universe u v w z

namespace Thomason.OmegaCategory

open CategoryTheory Limits ConcreteCategory

namespace FilteredColimit

variable {J : Type u} [Category.{u} J] (F : J ⥤ OmegaCategory.{u})

variable [IsFiltered J]

lemma unit_left (k : ℕ) (x : Cell F)
    (h : target F k (source F k x) = source F k x) :
    comp F k (source F k x) x h = x := by
  obtain ⟨j, a, rfl⟩ := exists_rep F x
  simp only [source_ι] at h ⊢
  rw [comp_ι F k j _ _ ((F.obj j).target_source_self k a), (F.obj j).unit_left]

end FilteredColimit
end Thomason.OmegaCategory
end
end OAI
