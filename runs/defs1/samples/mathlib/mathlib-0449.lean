@[expose] public section

namespace CategoryTheory.MonoidalCategory

variable (C D : Type*)

variable [Category* C] [MonoidalCategory C] [Category* D]

attribute [local instance] endofunctorMonoidalCategory

attribute [local aesop safe apply (rule_sets := [CategoryTheory])]
  MonoidalOpposite.hom_ext

namespace MonoidalRightAction

variable {C D}

/-- If the action of `C` on `D` comes from a monoidal functor `C ⥤ (D ⥤ D)`,
then `curriedActionMop C D` is naturally isomorphic to that functor. -/
@[simps!]
def curriedActionActionOfMonoidalFunctorToEndofunctorIso
    (F : C ⥤ (D ⥤ D)) [F.Monoidal] :
    letI := actionOfMonoidalFunctorToEndofunctor F
    curriedAction C D ≅ F :=
  .refl _

end MonoidalRightAction
end CategoryTheory.MonoidalCategory
end
