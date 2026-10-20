public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v v' u u' t

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w} D]

@[simp]
theorem extLinearEquivOfEquivalence_apply (R : Type t) [Ring R] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] {X Y : C} {n : ℕ}
    (α : Ext.{w} X Y n) :
    extLinearEquivOfEquivalence R e X Y n α = α.mapExactFunctor e.functor :=
  e.extAddEquiv_apply α

end TauCeti
end
