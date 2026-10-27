public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.RootSystem TauCeti.GLSymplecticFin CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld.Transvection.Pres

open scoped commutatorElement

variable {n : ℕ} {K : Type} [Field K]

namespace SpRelations

variable {G : Type*} [Group G] (R : SpRelations n K G)

theorem toEps_rt {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) (c : K) :
    R.toEps (rt a b) c = R.ξ a b c := by
  rw [← stdVec_rtIdx hab, toEps_stdVec]
  rcases eq_sp_of_rt_eq (stdVec_rtIdx hab).symm with h | h
  · rw [← h]
  · rw [← h, R.symm a b hab]

end SpRelations
end CFSG.Timmesfeld.Transvection
end
