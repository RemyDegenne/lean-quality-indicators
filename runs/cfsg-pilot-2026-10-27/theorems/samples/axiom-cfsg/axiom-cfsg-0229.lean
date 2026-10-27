public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open Matrix Equiv CFSG.SectionRank.OddCover CFSG.Quasithin

variable {F : Type} [Field F]

variable {C : Type} [CommGroup C]

theorem det_coe_monEmb (e : C →* Fˣ) {m : ℕ} (x : Mon C m) :
    ((monEmb (F := F) e m x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).det =
      (e (monDet x) : F) * ((Perm.sign (monPerm x) : ℤ) : F) := by
  have hdet : monDet x = ∏ i, x.left i := by
    conv_lhs => rw [mon_eq_monT_mul_monS x]
    rw [map_mul, monDet_monT, monDet_monS, mul_one]
  rw [monEmb_apply, Units.val_mul, det_mul, det_diagHom, coe_monPermGL, det_permutation,
    Perm.sign_inv, hdet, map_prod, Units.coe_prod]
  rfl

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
end
