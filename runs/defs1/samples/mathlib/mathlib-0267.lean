@[expose] public section

noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable {J : Type w} (f : J → C)

section

variable [HasCoproduct f]

/-- If `G` preserves coproducts and `C` has them,
then the cofan constructed of the mapped inclusion of a coproduct is a colimit.
-/
def isColimitOfHasCoproductOfPreservesColimit [PreservesColimit (Discrete.functor f) G] :
    IsColimit (Cofan.mk _ fun j : J => G.map (Sigma.ι f j) : Cofan fun j => G.obj (f j)) :=
  isColimitCofanMkObjOfIsColimit G f _ (coproductIsCoproduct _)

end
end CategoryTheory.Limits
end
end
