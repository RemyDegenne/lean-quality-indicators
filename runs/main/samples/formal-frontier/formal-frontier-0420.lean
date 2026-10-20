@[expose] public section

set_option warningAsError true

universe u v

namespace Matrix.DualNumberMixedSLCommutator

open Matrix.DualNumberKernels Matrix.DualNumberMixedCommutator

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

@[simp] theorem mixedSLKernel_snd_snd (X Y : LieAlgebra.SpecialLinear.sl n R) (i j : n) :
    (((mixedSLKernel X Y).1 : Matrix n n (DualNumber (DualNumber R))) i j).snd.snd =
      (⁅X, Y⁆ : LieAlgebra.SpecialLinear.sl n R).1 i j := by
  rw [← slReadback_apply, mixedSLKernel_readback]
  rfl

end Matrix.DualNumberMixedSLCommutator
end
