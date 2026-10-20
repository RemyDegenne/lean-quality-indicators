public section

set_option warningAsError true

set_option linter.style.haveILetI false

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    {C : Type (v + 1)} [Category.{v} C]
    (N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C) (i0 : ι)
    (U0 : Opens (N.obj (op i0)))

omit [IsDirectedOrder ι] in
theorem spectralStage
    (hstage : ∀ k : ιᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget C).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget C).map f))
    (hU0 : IsCompact (U0 : Set (N.obj (op i0)))) (i : (Set.Ici i0)ᵒᵖ) :
    SpectralSpace ((restricted N i0 U0 ⋙ SheafedSpace.forget C).obj i) := by
  letI : SpectralSpace (N.obj (op (unop i).1)) := hstage (op (unop i).1)
  have hc : IsCompact (stageOpen N i0 U0 (unop i) : Set (N.obj (op (unop i).1))) := by
    let base : Set.Ici i0 := ⟨i0, le_refl i0⟩
    let f : i ⟶ op base := (homOfLE (show base ≤ unop i from (unop i).2)).op
    have heq := stageOpen_map N i0 U0 f
    rw [stageOpen_base N i0 U0] at heq
    rw [heq]
    have hspectral : IsSpectralMap ((tailDiagram N i0).map f).hom.base :=
      htransition ((tailInclusion i0).op.map f)
    simpa only [Opens.map_coe] using hU0.preimage_of_isOpen hspectral U0.isOpen
  have hcarrier : ((restricted N i0 U0 ⋙ SheafedSpace.forget C).obj i) =
      (Opens.toTopCat (N.obj (op (unop i).1))).obj (stageOpen N i0 U0 (unop i)) := rfl
  rw [hcarrier]
  letI : CompactSpace ((Opens.toTopCat (N.obj (op (unop i).1))).obj
      (stageOpen N i0 U0 (unop i))) :=
    isCompact_univ_iff.mp
      ((stageOpen N i0 U0 (unop i)).isOpenEmbedding.isCompact_iff.mpr (by
        simpa only [Set.image_univ, Opens.set_range_inclusion'] using hc))
  exact (stageOpen N i0 U0 (unop i)).isOpenEmbedding.spectralSpace

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
end
end
