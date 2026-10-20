@[expose] public section

namespace CategoryTheory

open Category

variable {C D : Type*} [Category* C] [Category* D]

namespace ObjectProperty

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) [F.Full] [F.Faithful]

include adj

lemma isLocal_iff_isIso_map {X Y : D} (f : X ⟶ Y) :
    isLocal (· ∈ Set.range F.obj) f ↔ IsIso (G.map f) := by
  have := adj.unit.naturality f
  dsimp at this
  rw [← (isLocal (· ∈ Set.range F.obj)).postcomp_iff _ _ (isLocal_adj_unit_app adj Y),
    this, (isLocal (· ∈ Set.range F.obj)).precomp_iff _ _ (isLocal_adj_unit_app adj X),
    isLocal_iff_isIso _ _ ⟨_, rfl⟩ ⟨_, rfl⟩]
  exact ⟨fun _ ↦ isIso_of_fully_faithful F (G.map f), fun _ ↦ inferInstance⟩

end
end ObjectProperty
end CategoryTheory
end
