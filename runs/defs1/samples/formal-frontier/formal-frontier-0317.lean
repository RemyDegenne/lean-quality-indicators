@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The finite p-power system is the existing supported-residue system
precomposed with p-power indexing. -/
def pPowerResidueFiniteFunctor (p : Nat.Primes) : ℕᵒᵈ ⥤ FiniteGrp.{u} :=
  pPowerIndex p ⋙ residueFiniteFunctor.{u} {p}

end ProfiniteGrp
end
