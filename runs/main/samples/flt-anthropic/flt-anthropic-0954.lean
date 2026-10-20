set_option autoImplicit false

noncomputable section

universe u v w

namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R] {τ : Type v} {τ' : Type w}

variable {p}

omit hp [CommRing R] in
@[simp] theorem pairSeries_one (a b : ℕ → MvPowerSeries τ R) (m : ℕ) :
    pairSeries a b (1, m) = b m := rfl

end WittLaw
end MvFormalGroup
end
