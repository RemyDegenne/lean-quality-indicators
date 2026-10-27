public noncomputable section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.Quasithin.H13.F48Gen CFSG.D4Hex
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion

namespace HexGeomOf

variable {S : LieSetting.{0, 0}} {K : Type} [Group K] [MulAction K (Fin 819)]
  [MulAction K (Fin 2457)] {Φ : K →* S.ι.G0} {Ψ : S.ι.G0 →* K} (Gm : HexGeomOf S K Φ Ψ)

theorem κ_phi (x : K) (z : Pt S.ι) : Gm.κ (Φ x • z) = x • Gm.κ z := by
  have h1 := Gm.e_smul x (Sum.inl z)
  rw [CosetGeom.smul_inl, Gm.e_κ, Gm.e_κ] at h1
  exact Sum.inl_injective h1

end HexGeomOf
end CFSG.Quasithin.D4Hex
end
