@[expose] public section

open Function Set

variable {X X' : Type*} {Y Y' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

@[simp, mfld_simps] theorem symm_symm : e.symm.symm = e := rfl

end OpenPartialHomeomorph
end
