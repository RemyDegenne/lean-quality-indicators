@[expose] public section

open Set

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp]
theorem primewisePadicIdealOfExponents_zero :
    primewisePadicIdealOfExponents.{u} 0 = ⊤ := by
  ext x
  simp

end ProfiniteGrp
end
