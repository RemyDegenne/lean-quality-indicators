@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat

universe u w

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    (F : I ⥤ FintypeCat.{max u w})

variable {F}

variable {S T : FintypeCat.{max u w}}

/-- Target postcomposition on the filtered colimit of stage maps. -/
noncomputable def stageHomPost (t : S ⟶ T) :
    colimit (stageHom F S) ⟶ colimit (stageHom F T) :=
  (stageHomFunctor F).map t

end Profinite
end
