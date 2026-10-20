@[expose] public section

set_option warningAsError true

universe uR uJ uM uN

namespace AdicCompletion

variable {R : Type uR} [CommRing R] (I : Ideal R)
  {J : Type uJ} (M : J → Type uM)
  [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]

variable {M} {N : J → Type uN}
  [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]

@[simp]
theorem piEquivOfFG_symm_map (hI : I.FG) (f : ∀ j, M j →ₗ[R] N j)
    (x : ∀ j, AdicCompletion I (M j)) :
    (piEquivOfFG I N hI).symm (fun j ↦ map I (f j) (x j)) =
      map I (LinearMap.piMap f) ((piEquivOfFG I M hI).symm x) := by
  apply (piEquivOfFG I N hI).injective
  rw [LinearEquiv.apply_symm_apply, piEquivOfFG_apply, pi_map,
    ← piEquivOfFG_apply I M hI, LinearEquiv.apply_symm_apply]

end AdicCompletion
end
