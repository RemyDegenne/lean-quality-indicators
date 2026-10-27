public section

open CategoryTheory Limits

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

section Global

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {M N : SheafOfModules.{u} R}

/-- Presentations of `M` and of `N` give a presentation of `M ⊞ N`: its generators and its
relations are indexed by the disjoint unions of those of `M` and `N`. -/
@[expose]
def _root_.SheafOfModules.Presentation.biprod (P : M.Presentation) (Q : N.Presentation) :
    (M ⊞ N).Presentation :=
  presentationOfIsCokernelFree
    ((freeBiprodIso _ _).inv ≫
      biprod.map ((freeHomEquiv _).symm P.relations.s ≫ kernel.ι _)
        ((freeHomEquiv _).symm Q.relations.s ≫ kernel.ι _) ≫ (freeBiprodIso _ _).hom)
    ((freeBiprodIso _ _).inv ≫ biprod.map P.generators.π Q.generators.π)
    (by
      have h : Limits.biprod.map ((freeHomEquiv _).symm P.relations.s ≫ kernel.ι _)
          ((freeHomEquiv _).symm Q.relations.s ≫ kernel.ι _) ≫
            Limits.biprod.map P.generators.π Q.generators.π = 0 := by
        apply biprod.hom_ext' <;> simp
      simp [h]) <|
  IsCokernel.ofIso _ (CokernelCofork.isColimitBiprod P.isColimit Q.isColimit) _
    (freeBiprodIso _ _) (freeBiprodIso _ _) (Iso.refl _) (by simp) (by simp)

end Global
end SheafOfModules
end
end TauCeti
end
