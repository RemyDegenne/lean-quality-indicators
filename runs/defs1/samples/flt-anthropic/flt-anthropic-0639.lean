namespace P2MW.S_MvFormalGroup_CartierModule_eq_of_map_eq

set_option autoImplicit false

noncomputable section

open MvPowerSeries

universe u

namespace P2mKcCartierFaithful

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R]

variable {d d' : ℕ}

section Descent

variable [CharP R p] {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

def seq (δ : Φ.Hom Φ') : ℕ → Fin d' → MvPowerSeries (Fin d) R
  | 0 => δ.toPowerSeries
  | r + 1 => fun i => contract p (seq δ r i)

end Descent
end P2mKcCartierFaithful
end
end P2MW.S_MvFormalGroup_CartierModule_eq_of_map_eq
