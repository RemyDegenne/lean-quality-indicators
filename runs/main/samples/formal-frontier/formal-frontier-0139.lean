set_option warningAsError true

@[expose] public section

namespace Steinberg

universe uι uR uG

open scoped commutatorElement

variable {ι : Type uι} {R : Type uR} [Ring R]

section Elementary

variable [Fintype ι] [DecidableEq ι]

@[simp]
theorem toGL_generator (p : Root ι) (a : R) :
    toGL (generator p a) =
      Matrix.GeneralLinearGroup.elementaryUnit p.1.1 p.1.2 p.2 a := by
  simp [toGL, elementaryGenerator]

end Elementary
end Steinberg
end
