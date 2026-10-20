@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C D H H' : Type _} [Category* C] [Category* D] [Category* H] [Category* H']
  (LF'' LF' LF : D ⥤ H) {F F' F'' : C ⥤ H} (e : F ≅ F') {L : C ⥤ D}
  (α'' : L ⋙ LF'' ⟶ F'') (α' : L ⋙ LF' ⟶ F') (α : L ⋙ LF ⟶ F) (α'₂ : L ⋙ LF' ⟶ F)
  (W : MorphismProperty C)

variable (F)

variable (L)

variable [L.IsLocalization W]

variable {F}

variable (F)

variable {F L W}

section

variable (F) [F.HasLeftDerivedFunctor W] (L W)

/-- The canonical natural transformation `L ⋙ F.totalLeftDerived L W ⟶ F`. -/
noncomputable def totalLeftDerivedCounit : L ⋙ F.totalLeftDerived L W ⟶ F :=
  have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtensionCounit L F

end
end Functor
end CategoryTheory
end
