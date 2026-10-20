public section

namespace TauCeti.BraidWord

open BraidGroup

variable {n : ℕ}

theorem crossinglessComponents_closure_insert_pair (u v : BraidWord n)
    (i : Fin (n - 1)) (ε η : ℤˣ) :
    (u ++ [(i, ε), (i, η)] ++ v).closure.crossinglessComponents +
        Multiset.replicate (if (u ++ v).crossingsAt (strand i) = [] then 1 else 0) true +
        Multiset.replicate (if (u ++ v).crossingsAt (strandSucc i) = [] then 1 else 0) true =
      (u ++ v).closure.crossinglessComponents := by
  rw [crossinglessComponents_closure, crossinglessComponents_closure,
    ← Multiset.replicate_add, ← Multiset.replicate_add]
  exact congrArg (fun k => Multiset.replicate k true)
    (by simpa only [crossinglessComponentCount_closure] using
      crossinglessComponentCount_closure_insert_pair u v i ε η)

end TauCeti.BraidWord
end
