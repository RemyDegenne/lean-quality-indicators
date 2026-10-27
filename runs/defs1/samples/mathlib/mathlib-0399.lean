@[expose] public section

variable {F α M N G : Type*}

namespace Units

variable [Monoid M] [Monoid N]

/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
  { map h.toMonoidHom with
    invFun := map h.symm.toMonoidHom,
    left_inv := fun u => ext <| h.left_inv u,
    right_inv := fun u => ext <| h.right_inv u }

end Units
end
