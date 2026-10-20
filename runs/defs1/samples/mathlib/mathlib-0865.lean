@[expose] public section

namespace PowerSeries

variable
  {A : Type*} [CommRing A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S]

open MvPowerSeries.WithPiTopology

variable {f g : MvPowerSeries τ R}

variable {υ : Type*} {T : Type*} [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]

variable {a : MvPowerSeries τ S} {b : S⟦X⟧}

variable {a : PowerSeries S} {b : MvPowerSeries υ T} [IsScalarTower R S T]

section substInv

section Invertible

variable (P : R⟦X⟧) (hP : P.constantCoeff = 0) [Invertible (coeff 1 P)]

open PowerSeries

/-- Given a power series `P = u • X + O(X²)` with `u` invertible,
this is the construction of a power series `Q` such that `P(Q(X)) = X`. -/
noncomputable
def substInvFun : ℕ → R
  | 0 => 0
  | 1 => ⅟(P.coeff 1)
  | n + 1 => - ⅟(P.coeff 1) *
      (coeff (n + 1) (P.subst (∑ i : Fin (n + 1), C (substInvFun i.1) * X ^ i.1)))

end Invertible
end substInv
end PowerSeries
end
