@[expose] public section

universe v' v u' u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : Type u'} [Category.{v'} J]

namespace Limits

attribute [local instance] IsFiltered.isConnected

section

variable [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] [HasZeroMorphisms C]
  (S : ShortComplex (J ⥤ C)) (hS : S.Exact)
  {c₁ : Cocone S.X₁} (hc₁ : IsColimit c₁) (c₂ : Cocone S.X₂) (hc₂ : IsColimit c₂)
  (c₃ : Cocone S.X₃) (hc₃ : IsColimit c₃)
  (f : c₁.pt ⟶ c₂.pt) (g : c₂.pt ⟶ c₃.pt)
  (hf : ∀ j, c₁.ι.app j ≫ f = S.f.app j ≫ c₂.ι.app j)
  (hg : ∀ j, c₂.ι.app j ≫ g = S.g.app j ≫ c₃.ι.app j)

set_option backward.defeqAttrib.useBackward true in
/-- Given `S : ShortComplex (J ⥤ C)` and (colimit) cocones for `S.X₁`, `S.X₂`,
`S.X₃` equipped with suitable data, this is the induced
short complex `c₁.pt ⟶ c₂.pt ⟶ c₃.pt`. -/
@[simps]
def colim.mapShortComplex : ShortComplex C :=
  ShortComplex.mk f g (hc₁.hom_ext (fun j ↦ by
    rw [reassoc_of% (hf j), hg j, comp_zero, ← NatTrans.comp_app_assoc, S.zero,
      zero_app, zero_comp]))

end
end Limits
end CategoryTheory
end
