@[expose] public section

universe w' w v₁ v₂ u₁ u₂

open CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace ObjectProperty

variable (P : ObjectProperty C)

variable {P}

lemma IsCodetecting.isIso_iff_of_epi (hP : IsCodetecting P)
    {X Y : C} (f : X ⟶ Y) [Epi f] :
    IsIso f ↔ ∀ (G : C) (_ : P G), Function.Surjective ((yoneda.obj G).map f.op) := by
  constructor
  · intro h
    rw [isIso_iff_coyoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine hP _ (fun A hA g ↦ existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_epi f, h₁, h₂]

end ObjectProperty
end CategoryTheory
end
