@[expose] public section

universe u v w z

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

@[simp] theorem unitsKerEquiv_snd (r : Multiplicative R) :
    ((unitsKerEquiv r).1 : DualNumber R).snd = Multiplicative.toAdd r := rfl

end Matrix.DualNumberKernels
end
