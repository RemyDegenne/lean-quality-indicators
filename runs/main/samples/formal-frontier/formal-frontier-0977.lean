public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency false

set_option linter.style.haveILetI false

namespace TopCat.Sheaf.PullbackLocalSections

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (F : Y.Sheaf (Type v))

theorem germ_stalkIso (x : X) (V : Opens Y) (hx : f x ∈ V) :
    F.presheaf.germ V (f x) hx ≫ (stalkIso f F x).hom =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
        (op V) ≫
        ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.germ
          ((Opens.map f).obj V) x hx := by
  simp [stalkIso, nativeStalkHom, TopCat.Presheaf.stalkPushforward_germ]

end TopCat.Sheaf.PullbackLocalSections
end
end
