public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

theorem wrBase_injective : Function.Injective wrBase := by
  intro p q h
  have h1 : p.1 = q.1 := by
    simpa [wrBase] using congrArg (fun g : A5WrTwo => g.left 1) h
  have h2 : p.2 = q.2 := by
    simpa [wrBase, ofAdd_one_ne_one] using
      congrArg (fun g : A5WrTwo => g.left (Multiplicative.ofAdd 1)) h
  exact Prod.ext h1 h2

end CFSG.EvenSporadicStandard.HNRecog.Harada
end
