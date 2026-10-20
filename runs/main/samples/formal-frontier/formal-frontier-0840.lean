@[expose] public section

universe uR uS uT uM uN uP uY

open CategoryTheory

namespace TopModuleCat

section Algebra

variable {R : Type uR} {S : Type uS} [CommSemiring R] [Semiring S] [Algebra R S]

theorem algebraMap_mulAction_eq_smul :
    (fun p : R × S ↦ algebraMap R S p.1 * p.2) = (fun p : R × S ↦ p.1 • p.2) := by
  funext p
  exact (Algebra.smul_def p.1 p.2).symm

end Algebra
end TopModuleCat
end
