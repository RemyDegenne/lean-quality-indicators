public section

open Module (finrank)

open scoped TensorProduct

open LinearMap (BilinForm)

open TauCeti

namespace Representation

open TauCeti.Representation

variable {G : Type*} [Monoid G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {W : Type*} [AddCommGroup W] [Module ℝ W]

variable {ρ : Representation ℂ G V} {σ : Representation ℝ G W}

variable (ρ) in
/-- **Realizability over `ℝ`**: `ρ` admits a real form on the carrier `Fin (finrank ℂ V) → ℝ`.
Pinning the carrier avoids a type existential; a real form on an arbitrary carrier is
`Representation.IsRealForm`, and every result about the indicator is proved from that more general
notion.

Pinning the carrier by the dimension costs nothing: the pinned carrier is finite-dimensional, so a
real form on it already forces `V` to be finite-dimensional
(`Representation.IsRealizableOverReal.finiteDimensional`), and conversely every real form on a
finite-dimensional carrier transports to the pinned one
(`Representation.IsRealForm.isRealizableOverReal`).  For an infinite-dimensional `V` the predicate
is therefore simply false -- `finrank ℂ V` is then `0` and the pinned carrier is the zero space --
and `Representation.IsRealForm` is the notion to use there. -/
def IsRealizableOverReal : Prop :=
  ∃ σ : Representation ℝ G (Fin (finrank ℂ V) → ℝ), IsRealForm ρ σ

end Representation
end
