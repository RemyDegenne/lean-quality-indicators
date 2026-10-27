public section

namespace CFSG.StandardType

namespace StdSubSp

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank TableBSymp CFSG.SeitzReduction.SymplecticPilot

open CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {K : Type} [Field K] {n : ℕ}

section Supp

variable {S : Set (Fin n ⊕ Fin n)}

theorem isQuasisimple_suppGroup_range {m : ℕ} {σ : Fin m → Fin n} (hσ : Function.Injective σ)
    (hK : 4 ≤ Nat.card K) (hm : 1 ≤ m) :
    CFSG.IsQuasisimple (suppGroup (K := K) (Set.range (Sum.map σ σ))) := by
  rw [← range_spEmbed hσ]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (spEmbed_injective hσ))
    (CFSG.LieType.Universal.Symplectic.isQuasisimple m K hm (Or.inl (Or.inr hK)))

end Supp
end StdSubSp
end CFSG.StandardType
end
