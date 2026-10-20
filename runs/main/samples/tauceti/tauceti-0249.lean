public section

namespace TauCeti

namespace IntegralLattice

theorem level_typeARootLattice_of_odd {n : ℕ} (hn : Odd n) :
    (typeARootLattice n).level = 2 * (n + 1) := by
  rw [level_typeARootLattice, (Nat.coprime_two_right.mpr hn).gcd_eq_one, Nat.div_one]

end IntegralLattice
end TauCeti
end
