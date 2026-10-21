namespace OAI

section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic

open Matrix Finset

lemma extendedKnot_last (N : ℕ) :
    extendedKnotLabels N (2*N+1)=(3*angle/2)^2 := by
  simp [extendedKnotLabels]

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic
end
end OAI
