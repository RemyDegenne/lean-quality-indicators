public section

namespace CFSG.Quasithin

namespace S153G93D

namespace HRows

open CFSG.Assembly.LowTwoRank (StatedSU)

variable {W : Type} [CommGroup W] [Finite W] {G₀ K S : Subgroup (MulAut W)} {a : MulAut W}
  {z : W}

theorem oneM22Code_holds :
    OneM22Code := by
  intro W _ _ G₀ K S a z h hK
  have h3 := CFSG.Quasithin.H.Mathieu.code22_mParam ⟨h.K_le, G₀_le_normalizer h⟩ hK
  have hle := mParam_G₀_le_two h
  omega

end HRows
end S153G93D
end CFSG.Quasithin
end
