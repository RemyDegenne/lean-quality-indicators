public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

open CFSG.Sporadic.SuzOddCore.SylowFacts CFSG.Sporadic.Schreier.Tits

open scoped commutatorElement

theorem mem_of_found_tabRep {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : Array Tab}
    {x : Tab} {g : Equiv.Perm (Fin n)} (hH : Enumerates H T.toList)
    (hf : found (indexOf T) T x = true) (hx : TabRep x g) : g ∈ H := by
  obtain ⟨y, hy, hyrep⟩ := hH.sound x (mem_of_found hf)
  rwa [hyrep.perm_eq hx] at hy

end CFSG.Sporadic.SuzOddCore
end
