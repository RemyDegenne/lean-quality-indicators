@[expose] public section

universe v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (X : C)

namespace Functor

variable {D : Type u'} [Category.{v'} D] (f : C ⥤ D)

namespace FullyFaithful

variable {f}

variable (hf : FullyFaithful f)

/-- `mulEquivAut` as an isomorphism between automorphism groups. -/
@[simps!]
noncomputable def autMulEquivOfFullyFaithful (X : C) :
    Aut X ≃* Aut (f.obj X) where
  toEquiv := Aut.isoEquiv.trans (hf.isoEquiv.trans Aut.isoEquiv.symm)
  map_mul' := by cat_disch

end FullyFaithful
end Functor
end CategoryTheory
end
