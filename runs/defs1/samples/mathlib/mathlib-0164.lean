@[expose] public section

open Function

universe u v

variable {α β : Type*}

open Finset

/-- A non-infinite type is a fintype. -/
@[instance_reducible]
noncomputable def fintypeOfNotInfinite {α : Type*} (h : ¬Infinite α) : Fintype α :=
  @Fintype.ofFinite _ (not_infinite_iff_finite.mp h)

end
