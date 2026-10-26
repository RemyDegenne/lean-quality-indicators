/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.NativeCylinderComparison
public import SheafCohomology.NativeSpectralCylinder

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Global sections of compact-open native cylinders

For a directed opposite diagram of spectral sheafed spaces with spectral
transition maps, the actual native comparison from the restricted-stage
sections to sections over a compact open cylinder is invertible.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} (Type v)) (i0 : ι)
    (m : Cone N) (hm : IsLimit m) (U0 : Opens (N.obj (op i0)))

private instance tailNonempty : Nonempty (Set.Ici i0) := ⟨⟨i0, le_refl i0⟩⟩

private instance tailDirected : IsDirectedOrder (Set.Ici i0) :=
  tailDirectedOrder i0

private instance tailFiltered : IsFiltered (Set.Ici i0) := inferInstance

/-- The actual restricted-cylinder comparison is invertible for compact open
sections of a spectral directed inverse system. -/
theorem isIso_restrictedGlobalSectionsComparison
    (hstage : ∀ k : ιᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f))
    (hU0 : IsCompact (U0 : Set (N.obj (op i0)))) :
    IsIso (restrictedGlobalSectionsComparison N i0 m hm U0) := by
  let R := restricted N i0 U0
  let cR := (SheafedSpace.forget (Type v)).mapCone (restrictedCone N i0 m U0)
  let hcR : IsLimit cR := restrictedSpaceIsLimit N i0 m hm U0
  have hRstage : ∀ k : (Set.Ici i0)ᵒᵖ,
      SpectralSpace ((R ⋙ SheafedSpace.forget (Type v)).obj k) :=
    spectralStage N i0 U0 hstage htransition hU0
  have hRtransition : ∀ {k l : (Set.Ici i0)ᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((R ⋙ SheafedSpace.forget (Type v)).map f) :=
    fun {_ _} f => spectralStageMap N i0 U0 hstage htransition hU0 f
  have hnative : IsIso (SheafedSpace.nativeGlobalSectionsComparison R cR hcR) :=
    SheafedSpace.isIso_nativeGlobalSectionsComparison R cR hcR hRstage hRtransition
  have hcomparison : restrictedGlobalSectionsComparison N i0 m hm U0 =
      SheafedSpace.nativeGlobalSectionsComparison R cR hcR ≫
        SheafedSpace.Γ.map (chosenLimitIso N i0 m hm U0).inv.op ≫
          eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen N i0 m U0)) := by
    apply colimit.hom_ext
    intro i
    rw [colimit_ι_restrictedGlobalSectionsComparison,
      ← Category.assoc, ← Category.assoc,
      SheafedSpace.colimit_ι_nativeGlobalSectionsComparison,
      ← SheafedSpace.Γ.map_comp, ← op_comp,
      chosenLimitIso_inv_projection]
  rw [hcomparison]
  exact IsIso.comp_isIso' hnative (IsIso.comp_isIso' inferInstance inferInstance)

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
