@[expose] public section

variable {R M N N' : Type*}

variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']

variable [Module R M] [Module R N] [Module R N']

namespace ExteriorAlgebra

open CliffordAlgebra hiding ι

theorem liftAlternating_ι_mul (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) (m : M)
    (x : ExteriorAlgebra R M) :
    liftAlternating (R := R) (M := M) (N := N) f (ι R m * x) =
    liftAlternating (R := R) (M := M) (N := N) (fun i => (f i.succ).curryLeft m) x := by
  dsimp [liftAlternating]
  rw [foldl_mul, foldl_ι]
  rfl

end ExteriorAlgebra
end
