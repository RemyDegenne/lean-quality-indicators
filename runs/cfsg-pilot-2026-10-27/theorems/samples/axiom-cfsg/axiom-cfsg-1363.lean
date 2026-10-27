public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.SmallWeyl

variable {ι V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

namespace RootFamily

variable (T : RootFamily ι V)

variable {T}

theorem datum_adj_iff (hT : T.Nondegenerate) {i j : ι} :
    (T.datum hT i).Adj (T.datum hT j) ↔ T.χ i (T.z j) = 1 := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  show T.χ j (T.z i) = 1
  rw [T.symm j i]
  exact h

end RootFamily
end CFSG.ClassicalInvolution.Balance
end
