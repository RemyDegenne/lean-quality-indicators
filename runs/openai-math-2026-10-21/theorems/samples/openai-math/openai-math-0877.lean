namespace OAI

section

namespace CriticalHoneycomb.Transfer.SpectralFamily

open Reflection RowExchange BoundaryJet

open scoped Matrix BigOperators

attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma localForward_cap_expand (A B : Local) (s t : Spin) (p : Pair) :
    (localForward A B s t*ᵥcap) p=
      ∑ v : Spin,∑ a : Spin,A (p.1,s) (a,v)*B (p.2,v) (a.rev,t)*Reflection.phase^(spinValue a) := by
  simp only [localForward,Matrix.sum_mulVec,Finset.sum_apply]
  apply Finset.sum_congr rfl;intro v hv
  rw [Matrix.mulVec,dotProduct,sum_cap]
  rfl

end CriticalHoneycomb.Transfer.SpectralFamily
end
end OAI
