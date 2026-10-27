@[expose] public section

open scoped Pointwise Topology

open Filter

section General

variable
  {k V P : Type*}
  [Field k] [LinearOrder k] [AddCommGroup V] [Module k V] [AddTorsor V P] [TopologicalSpace V]

open AffineSpace

variable (k) in
/-- The set of directions `v` for which the set has points arbitrarily far in directions near `v`.
-/
def asymptoticCone (s : Set P) : Set V := {v | ∃ᶠ p in asymptoticNhds k P v, p ∈ s}

end General
end
