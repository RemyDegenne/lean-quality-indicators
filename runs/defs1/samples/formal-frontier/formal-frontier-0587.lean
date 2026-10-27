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

variable {C : Type (v + 1)} [Category.{v} C]

/-- Inclusion of the tail at `j` in the tail at `i0`. -/
@[expose] def betweenTailInclusion (i0 j : ι) (h : i0 ≤ j) :
    Set.Ici j ⥤ Set.Ici i0 :=
  (show Monotone (fun k : Set.Ici j => (⟨k.1, h.trans k.2⟩ : Set.Ici i0)) from
    fun _ _ hk => hk).functor

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
end
end
