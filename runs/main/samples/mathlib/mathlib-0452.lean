@[expose] public section

open Set Filter

open Submodule Function

namespace IsArtinianRing

section CommSemiring

variable (R : Type*) [CommSemiring R] [IsArtinianRing R]

@[stacks 00J7]
lemma setOfPred_isMaximal_finite : {I : Ideal R | I.IsMaximal}.Finite := by
  have ⟨s, H⟩ := Finset.exists_inf_le (Subtype.val (p := fun I : Ideal R ↦ I.IsMaximal))
  refine Set.finite_def.2 ⟨s, fun p ↦ ?_⟩
  have ⟨q, hq1, hq2⟩ := p.2.isPrime.inf_le'.mp (H p)
  rwa [← Subtype.ext <| q.2.eq_of_le p.2.ne_top hq2]

end CommSemiring
end IsArtinianRing
end
