@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat

universe u w

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    (F : I ⥤ FintypeCat.{max u w})

variable {F}

@[simp]
theorem stageHomEquiv_symm_apply (c : Cone (F ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (S : FintypeCat.{max u w})
    (f : c.pt ⟶ FintypeCat.toProfinite.obj S) :
    stageHomToContinuous c S ((stageHomEquiv c hc S).symm f) = f :=
  (stageHomEquiv c hc S).apply_symm_apply f

end Profinite
end
