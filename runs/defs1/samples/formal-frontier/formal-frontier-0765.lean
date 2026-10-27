public section

noncomputable section

open Polynomial

open scoped TensorProduct

namespace Module.FiniteProjective

universe uR uS uM uN uL

variable (R : Type uR) (M : Type uM)
  [CommRing R] [AddCommGroup M] [Module R M]

/-- The characteristic polynomial obtained by reflecting the canonical
Fredholm polynomial at the prescribed constant rank. -/
noncomputable def finiteProjectiveCharpoly [Module.Finite R M]
    [Module.Projective R M] (n : ℕ) (f : Module.End R M) : R[X] :=
  (FreePresentation.fredholm (R := R) (M := M)
    (freePresentation R M) f).reflect n

end Module.FiniteProjective
end
end
