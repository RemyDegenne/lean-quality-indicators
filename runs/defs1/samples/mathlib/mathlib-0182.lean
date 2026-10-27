@[expose] public section

namespace CategoryTheory

open GrothendieckTopology Limits Opposite CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

variable {D : Type u₂} [Category.{v₂} D]

variable {E : Type*} [Category* E]

variable {F : D ⥤ E} {G : E ⥤ D}

namespace Sheaf

noncomputable section

/-- An adjunction `adj : G ⊣ F` with `F : D ⥤ E` and `G : E ⥤ D` induces an adjunction
between `Sheaf J D` and `Sheaf J E`, in contexts where one can sheafify `D`-valued presheaves,
and postcomposing with `F` preserves the property of being a sheaf. -/
def adjunction [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F) :
    composeAndSheafify J G ⊣ sheafCompose J F :=
  Adjunction.restrictFullyFaithful ((adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J D))
    (fullyFaithfulSheafToPresheaf J E) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

end
end Sheaf
end CategoryTheory
end
