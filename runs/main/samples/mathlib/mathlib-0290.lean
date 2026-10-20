@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

namespace HomologicalComplex

variable {V}

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

open ZeroObject

noncomputable section

theorem kernel_eq_kernel [HasKernels V] {i j j' : ι} (r : c.Rel i j) (r' : c.Rel i j') :
    kernelSubobject (C.d i j) = kernelSubobject (C.d i j') := by
  rw [← d_comp_eqToHom C r r']
  apply kernelSubobject_comp_mono

end
end HomologicalComplex
end
