public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.A6

open CFSG.Quasithin.H13.L32A

open scoped IsMulCommutative

variable {G : Type} [Group G]

variable [Finite G]

namespace XCtx

variable {T L V V₂ X : Subgroup G} {g : G}

variable {C : XCtx G T L V V₂ X g} (K : C.Coords)

theorem Coords.toAdd_e_conjW (h : ↥(lOne L V₂ ⊔ X ⊔ T)) (w : ↥⁅V₂, X⁆) :
    Multiplicative.toAdd (K.e (conjW C h w)) =
      ((K.φ h : SL3.S) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (Multiplicative.toAdd (K.e w)) := by
  rw [repV_mulVec C.H3_le_normalizer K.e h w (conjW C h w) rfl, toAdd_ofAdd]
  rfl

end XCtx
end CFSG.Quasithin.H13.L14413
end
