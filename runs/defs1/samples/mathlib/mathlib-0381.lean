@[expose] public section

namespace CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C]

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WithTerminal

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WithInitial

namespace WithTerminal

variable {C}

/-- A natural isomorphism between the functor `map (F ⋙ G) ` and `map F ⋙ map G `. -/
@[simps!]
def mapComp {D E : Type*} [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) ≅ map F ⋙ map G :=
  NatIso.ofComponents (fun X => match X with
    | of _ => Iso.refl _
    | star => Iso.refl _) (by cat_disch)

end WithTerminal
end CategoryTheory
end
