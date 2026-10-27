public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree.J2Tab

open CFSG.Sporadic.J1.Native (mulL idL colsL dotL)

open CFSG.KC.ListGroup (grp)

theorem sx_chk (X : List (List ℕ)) (hX : colsL 14 X = xC) (p : Fin 3 × Fin 3 × Fin 3) :
    mulL 5 14 (FT p) X = FT (p.1 + 1, p.2.1, p.2.2 - p.2.1) := by
  rw [mulL_eq, hX]
  exact eq_of_beq (sx_chkB p)

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree.J2Tab
end
