@[expose] public section

universe u v w x

namespace Module

section Ring

variable (R : Type u) [Ring R]

variable (M : Type v) [AddCommGroup M] [Module R M]

variable {R M}

theorem IsCoherent.ker {N : Type w} [AddCommGroup N] [Module R N]
    [Module.IsCoherent R M] [Module.IsCoherent R N] (f : M →ₗ[R] N) :
    Module.IsCoherent R (LinearMap.ker f) := by
  let _ : Module.IsCoherent R (LinearMap.range f) := IsCoherent.range f
  have hker : (LinearMap.ker f.rangeRestrict).FG :=
    Module.FinitePresentation.fg_ker f.rangeRestrict
      (LinearMap.surjective_rangeRestrict f)
  rw [LinearMap.ker_rangeRestrict] at hker
  exact IsCoherent.submodule _ hker

end Ring
end Module
end
