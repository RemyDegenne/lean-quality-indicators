public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

theorem linearAdicReduction_surjective (I : Ideal R) (k : ℕ) :
    Function.Surjective (linearAdicReduction (σ := σ) I k) :=
  adicReduction_surjective I k

end MvPowerSeries
end
