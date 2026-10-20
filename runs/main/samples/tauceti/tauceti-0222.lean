public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Polynomial Functor.LaxMonoidal Functor.OplaxMonoidal

variable (R : Type u) [CommRing R] {i n : ℕ}

theorem powerXOfLE_baseChange_acyclic (hi : i ≤ n) :
    ((toPeriodicComplex (AdjoinRoot.mk (X ^ n : R[X])) AdjoinRoot.mk_self).obj
      (powerXOfLE R hi)).Acyclic := by
  intro j
  exact (powerXPeriodicComplex_acyclic R hi j).of_iso
    (powerXOfLEBaseChangePeriodicIso R hi).symm

end TauCeti.MatrixFactorization
end
end
