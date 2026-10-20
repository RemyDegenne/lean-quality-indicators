@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat

universe u w

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    (F : I ⥤ FintypeCat.{max u w})

variable {F}

theorem exists_stageHomClass (c : Cone (F ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (S : FintypeCat.{max u w})
    (f : c.pt ⟶ FintypeCat.toProfinite.obj S) :
    ∃ (i : I) (g : F.obj i ⟶ S),
      stageHomToContinuous c S (stageHomClass F S i g) = f := by
  obtain ⟨i, g, rfl⟩ := exists_hom c hc f
  exact ⟨i, g, stageHomToContinuous_class c S i g⟩

end Profinite
end
