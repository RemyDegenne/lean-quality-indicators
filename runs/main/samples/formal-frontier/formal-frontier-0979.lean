@[expose] public section

set_option warningAsError true

universe uR uJ uM uN

namespace AdicCompletion

variable {R : Type uR} [CommRing R] (I : Ideal R)
  {J : Type uJ} {M : J → Type uM} {N : J → Type uN}
  [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
  [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]

theorem pi_comp_map (f : ∀ j, M j →ₗ[R] N j) :
    pi I N ∘ₗ map I (LinearMap.piMap f) =
      LinearMap.piMap (fun j ↦ map I (f j)) ∘ₗ pi I M := by
  simp only [pi, LinearMap.piMap, LinearMap.pi_comp, LinearMap.comp_assoc,
    LinearMap.proj_pi, map_comp]

end AdicCompletion
end
