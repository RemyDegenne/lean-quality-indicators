public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w w' v v' u u'

namespace TriangulatedK0

open CategoryTheory.Pretriangulated

section UniversalProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [EssentiallySmall.{w} C]
  {G : Type*} [AddCommGroup G]

namespace ShiftInvariant

variable {e : C ≌ C} [e.functor.CommShift ℤ] [e.functor.IsTriangulated]
  {σ : AddAut G}

@[simp]
lemma liftEquiv_apply (a : ShiftInvariant C e σ) :
    (liftEquiv e σ a).1 = a.lift :=
  (rfl)

end ShiftInvariant
end UniversalProperty
end TriangulatedK0
end TauCeti
end
