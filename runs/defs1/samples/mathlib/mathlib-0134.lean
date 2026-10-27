@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

namespace HomologicalComplex

variable {V}

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

open ZeroObject

section

variable (V c)

/-- The functor forgetting the differential in a complex, obtaining a graded object. -/
@[simps, implicit_reducible]
def forget : HomologicalComplex V c ⥤ GradedObject ι V where
  obj C := C.X
  map f := f.f

end
end HomologicalComplex
end
