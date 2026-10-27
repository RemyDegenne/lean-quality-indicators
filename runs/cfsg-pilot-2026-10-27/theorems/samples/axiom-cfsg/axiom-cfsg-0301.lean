public section

namespace CFSG.SectionRank.QTK.Insp443.PermKit

open Equiv CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

open scoped Matrix

variable {n : ℕ}

theorem sum_maskVec_eq_ind_bsum {rows : List ℕ} {k : ℕ} (hrows : rows.length = k) (m p : ℕ) :
    ∑ i : Fin k, maskVec k m i * rowBit rows i p = if bsum rows m p then (1 : ZMod 2) else 0 := by
  rw [ind_bsum, hrows]
  exact Fin.sum_univ_eq_sum_range (fun i => mbit m i * rowBit rows i p) k

end CFSG.SectionRank.QTK.Insp443.PermKit
end
