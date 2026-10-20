@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

namespace ShortComplex

variable {S S₁ S₂ : ShortComplex C}

/-- Given a right homology map data `ψ : RightHomologyMapData φ h₁ h₂` such that
both right homology data `h₁` and `h₂` are preserved by a functor `F`, this is
the induced right homology map data for the morphism `F.mapShortComplex.map φ`. -/
@[simps]
noncomputable def RightHomologyMapData.map {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData}
    {h₂ : S₂.RightHomologyData} (ψ : RightHomologyMapData φ h₁ h₂) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h₁.IsPreservedBy F] [h₂.IsPreservedBy F] :
    RightHomologyMapData (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) where
  φQ := F.map ψ.φQ
  φH := F.map ψ.φH
  commp := by simpa only [F.map_comp] using! F.congr_map ψ.commp
  commg' := by simpa only [RightHomologyData.map_g', F.map_comp] using! F.congr_map ψ.commg'
  commι := by simpa only [F.map_comp] using! F.congr_map ψ.commι

end ShortComplex
end CategoryTheory
end
