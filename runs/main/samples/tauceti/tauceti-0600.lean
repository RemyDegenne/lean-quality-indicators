public section

namespace TauCeti

open Polynomial

universe u v

variable {F : Type u} [Field F]

theorem natCard_gal_dvd_factorial_natDegree (p : F[X]) :
    Nat.card p.Gal ∣ p.natDegree.factorial := by
  exact (natCard_gal_dvd_factorial_card_rootSet p).trans
    (Nat.factorial_dvd_factorial <| by
      rw [Set.fintypeCard_eq_ncard]
      exact Polynomial.ncard_rootSet_le p p.SplittingField)

end TauCeti
end
