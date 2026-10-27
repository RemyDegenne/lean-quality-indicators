set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace LinearEquiv

universe u v

/-- The inverse image under `e` of `(0,p)` identifies `P` with the
kernel of the coefficient row recovered from `e`. -/
noncomputable def coefficientProductRowKernelEquiv (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) :
    P ≃ₗ[R] LinearMap.ker (Bass.coefficientRowScalarMap R 2 (coefficientProductRow R P e)) :=
  ((LinearEquiv.ofLeftInverse (f := LinearMap.inr R R P)
      (g := LinearMap.snd R R P) (by intro p; rfl)).trans
    (LinearEquiv.ofEq _ _ (LinearMap.range_inr R R P))).trans
    ((Bass.kernelEquivOfLinearEquiv
      (Bass.coefficientRowScalarMap R 2 (coefficientProductRow R P e))
      (LinearMap.fst R R P) e (fun x ↦ (coefficientProductRow_apply R P e x).symm)).symm)

end LinearEquiv
end
