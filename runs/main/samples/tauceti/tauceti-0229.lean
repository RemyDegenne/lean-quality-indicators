public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (k : Type t) (e : C ≌ C)

section FieldSource

variable [Field k] [Linear k C] [e.functor.Additive] [e.functor.Linear k]

variable {k e}

variable {X Y : C}

theorem IsGradedExtInternallyFinite.shiftSourceInverse
    (h : IsGradedExtInternallyFinite.{w} k e X Y) :
    IsGradedExtInternallyFinite.{w} k e (e.inverse.obj X) Y :=
  ⟨fun n => (h.finiteLaurentSupport n).gradedExtShiftSourceInverse⟩

end FieldSource
end TauCeti
end
