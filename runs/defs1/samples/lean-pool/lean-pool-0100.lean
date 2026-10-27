@[expose] public section

open Polynomial

open Set

open Multiset

open Complex

open scoped Polynomial

open scoped BigOperators

local notation "rexp" => Real.exp

local notation "π" => Real.pi

noncomputable section

/-- The map `t ↦ e^(∑_{x ∈ t} x)` on multisets of complex numbers. -/
def cexpMultisetSum : Multiset ℂ → ℂ := fun t ↦ cexp t.sum

end
end
