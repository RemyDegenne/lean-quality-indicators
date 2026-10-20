public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.TypeDSpinCarrier

universe v

variable (n : ℕ) (hn : 4 ≤ n)

theorem rootIntMatrix_apply_of_eq (j : Fin n ⊕ Fin n)
    {a a' : Fin (dimension n)} {c : ℤˣ}
    (h : rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.D n) j))
        (latticeBasis n a : ExteriorAlgebra ℚ (polarization n).W) =
      c • (latticeBasis n a' : ExteriorAlgebra ℚ (polarization n).W)) (r : Fin (dimension n)) :
    rootIntMatrix n hn j r a = if r = a' then (c : ℤ) else 0 :=
  kostantRootGeneratorIntMatrix_apply_of_eq _ _ _ _ _ _ _ h r

end TauCeti.TypeDSpinCarrier
end
