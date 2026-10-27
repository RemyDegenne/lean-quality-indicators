set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

def dimShiftDownSC (X : ShortComplex (Rep.{u} k G)) : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (dimShiftDownObjMap X.f) (dimShiftDownObjMap X.g) (by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => Subtype.ext ?_))
    show (indBotMap X.g).hom ((indBotMap X.f).hom (x : X.X₁.indBot)) = 0
    rw [← Rep.comp_apply, show indBotMap X.f ≫ indBotMap X.g = 0 from (indBotSC X).zero]
    rfl)

end Rep
end
