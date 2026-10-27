@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat

universe u w

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    (F : I ⥤ FintypeCat.{max u w})

variable {F}

/-- A cocone of continuous maps, obtained by composing a stage map with its
projection from a cone. No limiting property is needed. -/
def stageHomCocone (c : Cone (F ⋙ FintypeCat.toProfinite))
    (S : FintypeCat.{max u w}) : Cocone (stageHom F S) where
  pt := c.pt ⟶ FintypeCat.toProfinite.obj S
  ι :=
    { app i := by
        cases i with
        | op i =>
          exact ↾fun (g : F.obj i ⟶ S) =>
            c.π.app i ≫ FintypeCat.toProfinite.map g
      naturality := by
        intro i j a
        cases i with
        | op i =>
          cases j with
          | op j =>
            ext g
            change c.π.app j ≫
              FintypeCat.toProfinite.map (F.map a.unop ≫ g) =
              c.π.app i ≫ FintypeCat.toProfinite.map g
            rw [FintypeCat.toProfinite.map_comp, ← Category.assoc]
            exact congrArg (fun h => h ≫ FintypeCat.toProfinite.map g) (c.w a.unop) }

end Profinite
end
