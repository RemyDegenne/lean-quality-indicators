public section

namespace TauCeti

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}

section AlgHom

variable [CommSemiring k] [AddCommMonoid V] [Module k V]

section Monoid

variable [Monoid G] {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ}

open TwistedMonoidAlgebra in
/-- **A projective representation with factor set `α` is a `k_α[G]`-module.** The algebra map is
the one the universal property of `TauCeti.twistedMonoidAlgebra` produces from the lift; a module
structure on `V` over an algebra is exactly such an algebra map to `Module.End k V`.

Writing the domain down needs the factor-set axioms, since `TauCeti.twistedMonoidAlgebra` takes
them as an instance argument; they are supplied by `h` itself, so no separate `IsFactorSet α`
instance need be in scope. -/
noncomputable def IsProjectiveRep.toAlgHom (h : IsProjectiveRep ρ α) :
    letI := h.isFactorSet
    twistedMonoidAlgebra k G α →ₐ[k] Module.End k V :=
  letI := h.isFactorSet
  lift (fun g ↦ (ρ g : V →ₗ[k] V)) (by rw [h.map_one]; rfl) h.toLinearMap_mul

end Monoid
end AlgHom
end TauCeti
end
