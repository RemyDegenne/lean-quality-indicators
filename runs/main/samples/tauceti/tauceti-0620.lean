public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v v' u u'

local instance {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] :
    (CategoryTheory.Prod.fst C D).PreservesZeroMorphisms where
  map_zero _ _ := rfl

local instance {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] :
    (CategoryTheory.Prod.snd C D).PreservesZeroMorphisms where
  map_zero _ _ := rfl

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]

namespace ExactStructure

variable (E : ExactStructure C) (E' : ExactStructure D)

@[simp]
theorem prod_isProjective_iff (Q : C × D) :
    (E.prod E').isProjective Q ↔ E.isProjective Q.1 ∧ E'.isProjective Q.2 := by
  simp only [isProjective_iff]
  constructor
  · intro hQ
    constructor
    · intro X Y p hp f
      obtain ⟨g, hg⟩ := hQ
        ((prod_isDeflation_iff E E'
          ((p, 𝟙 Q.2) : (X, Q.2) ⟶ (Y, Q.2))).mpr ⟨hp, E'.isDeflation_id _⟩)
        (f, 𝟙 Q.2)
      exact ⟨g.1, congrArg Prod.fst hg⟩
    · intro X Y p hp f
      obtain ⟨g, hg⟩ := hQ
        ((prod_isDeflation_iff E E'
          ((𝟙 Q.1, p) : (Q.1, X) ⟶ (Q.1, Y))).mpr ⟨E.isDeflation_id _, hp⟩)
        (𝟙 Q.1, f)
      exact ⟨g.2, congrArg Prod.snd hg⟩
  · rintro ⟨h₁, h₂⟩ X Y p hp f
    obtain ⟨hp₁, hp₂⟩ := (prod_isDeflation_iff E E' p).mp hp
    obtain ⟨g₁, hg₁⟩ := h₁ hp₁ f.1
    obtain ⟨g₂, hg₂⟩ := h₂ hp₂ f.2
    exact ⟨(g₁, g₂), Prod.hom_ext hg₁ hg₂⟩

end ExactStructure
end TauCeti
end
