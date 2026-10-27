public section

namespace CFSG.Quasithin

namespace RAV

variable {V : Type} [CommGroup V] [Finite V]

theorem rAV_conjAut {W : Type*} [CommGroup W] (g : MulAut W) (A : Subgroup (MulAut W)) :
    rAV (B1.conjAut g A) = rAV A := by
  have h1 : rk (B1.conjAut g A) = rk A := by
    unfold rk
    rw [B1.card_conjAut]
  have h2 : rkIdx (fixV (B1.conjAut g A)) = rkIdx (fixV A) := by
    unfold rkIdx
    rw [B1.fixV_conjAut]
    exact congrArg (padicValNat 2) (Subgroup.index_map_equiv (fixV A) g)
  unfold rAV
  rw [h1, h2]

end RAV
end CFSG.Quasithin
end
