@[expose] public section

universe w' w v₁ v₂ u₁ u₂

open CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

open ConcreteCategory

section ZeroMorphisms

variable [HasZeroMorphisms C]

lemma isCoseparator_of_isLimit_fan {β : Type w} {f : β → C}
    (hf : ObjectProperty.IsCoseparating (.ofObj f)) {c : Fan f} (hc : IsLimit c) :
    IsCoseparator c.pt := by
  rw [isCoseparator_def]
  refine fun _ _ _ _ huv ↦ hf _ _ (fun _ h g ↦ ?_)
  obtain ⟨b⟩ := h
  classical simpa using huv (hc.lift (Fan.mk _ (Pi.single b g))) =≫ c.proj b

end ZeroMorphisms
end CategoryTheory
end
