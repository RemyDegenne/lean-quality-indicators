public section

namespace CFSG.Quasithin.H13.I1277

open Certificates.Data.S1277Sig

theorem colsOf_one (d : Nat) : colsOf (1 : Equiv.Perm (Fin (2 ^ d))) = idCols d := by
  apply List.ext_getElem
  · rw [length_colsOf]; simp [idCols]
  · intro i h1 h2
    have hi : i < d := by simpa [length_colsOf] using h1
    rw [getElem_colsOf _ i hi]
    simp [idCols]

end CFSG.Quasithin.H13.I1277
end
