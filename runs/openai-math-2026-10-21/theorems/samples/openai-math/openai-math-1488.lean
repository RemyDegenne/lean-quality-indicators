namespace OAI

open Erdos970

noncomputable section

namespace Ostmann.Arithmetic.CanonicalHistoryLeafBulk

open Construction Conclusion

@[simp] theorem rows_length {n m : ℕ} (f : Fin n → Fin m → ℕ) :
    (rows f).length=n*m := by
  simp [rows,List.length_flatten,List.map_ofFn,Function.comp_def]

end Ostmann.Arithmetic.CanonicalHistoryLeafBulk
end
end OAI
