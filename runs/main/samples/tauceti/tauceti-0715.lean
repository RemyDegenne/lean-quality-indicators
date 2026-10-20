public section

universe w v u

namespace TauCeti.CurvedDuplex

open CategoryTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  (R : Type w) [Semiring R] [Linear R C]

@[simp]
theorem parityShiftToPeriodicComplexIso_hom_f_zero (X : CurvedDuplex C (0 : R)) :
    ((parityShiftToPeriodicComplexIso C R).hom.app X).f 0 = 𝟙 X.X₁ := by
  simp [parityShiftToPeriodicComplexIso]
  rfl

end TauCeti.CurvedDuplex
end
