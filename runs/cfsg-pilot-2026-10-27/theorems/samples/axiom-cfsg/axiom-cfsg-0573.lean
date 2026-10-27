public section

namespace CFSG.AGLEmbedding.ChevOuterD48

open CFSG.Quasithin

theorem size_frobPow (n : ℕ) (A : Array GF512) : (frobPow n A).size = A.size := by
  induction n with
  | zero => rfl
  | succ n ih => rw [frobPow, size_frobArr, ih]

end CFSG.AGLEmbedding.ChevOuterD48
end
