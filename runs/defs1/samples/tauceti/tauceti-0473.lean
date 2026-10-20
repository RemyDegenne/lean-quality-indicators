public section

namespace TauCeti.Hodge

universe u v

variable {V : Type u} {Vℂ : Type v}

variable [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V]

variable [AddCommGroup Vℂ] [Module ℂ Vℂ]

variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- A **point of the period domain** of the lattice `V` with the integral form `Qint`, at the Hodge
type `htype`: a weight-`n` Hodge structure of that type which the *fixed* form `Qint` polarizes.

The lattice is a finitely generated free `ℤ`-module, so the complexification is finite-dimensional
and the prescribed Hodge numbers really are the dimensions of the Hodge components.

The form does not vary with the point; it enters through the `Prop`-valued `IsPolarization` and so
is not carried twice.

The `Module.Free` and `Module.Finite` binders are spelled out on the header rather than left to the
surrounding `variable` block: automatic instance inclusion applies to theorems, not to a
`structure`, so omitting them would drop them from the signature entirely. -/
structure PeriodDomain.Point [Module.Free ℤ V] [Module.Finite ℤ V] (hℂ : IsBaseChange ℂ ιℂ)
    (n : ℤ) (Qint : LinearMap.BilinForm ℤ V) (htype : HodgeType) where
  /-- The varying datum: a Hodge filtration on the complexification. -/
  hs : HodgeStructure hℂ n
  /-- The Hodge type's weight is the weight of the structure. -/
  htype_weight : htype.weight = n
  /-- The fixed form polarizes the structure. -/
  pol : IsPolarization hℂ hs Qint
  /-- The structure realizes the prescribed Hodge numbers. -/
  hodge_numbers : ∀ p : ℤ, hs.hodgeNumber p = htype.h p

end TauCeti.Hodge
end
