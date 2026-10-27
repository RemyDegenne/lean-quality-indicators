public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

open scoped MatrixGroups commutatorElement

section Proof

variable {p f : ℕ} [Fact p.Prime]

theorem res25_of_parts (h0 : GCS25Z p f) (hd : DIAG25 p f) : RES25 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
    hn hn' hδ
  rcases Int.units_eq_one_or (diagChar hp hq e ⟨n, hn⟩) with h1 | h1
  · exact h0 G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
      hn hn' h1 (hδ.trans h1)
  · exact hd G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hnS
      hn hn' h1 (hδ.trans h1)

end Proof
end CFSG.ClassicalInvolution.Asc77.C25V
end
