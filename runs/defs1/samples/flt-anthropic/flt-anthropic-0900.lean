set_option autoImplicit false

section Kernel

open NumberField Matrix Topology

open scoped Classical

noncomputable section

namespace AutomorphicForm.StandardKernel

noncomputable def entryBox : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-3 : ℝ) 3

end AutomorphicForm.StandardKernel
end
end Kernel
