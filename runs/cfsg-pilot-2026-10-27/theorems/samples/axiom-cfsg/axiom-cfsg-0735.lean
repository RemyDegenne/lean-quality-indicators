public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

variable {G : Type} [Group G]

section Action

variable (Z U H : Subgroup G) (hHN : H ≤ Subgroup.normalizer (Z : Set G))
  (hHU : H ≤ Subgroup.normalizer (U : Set G))

theorem actTilde_apply (h : ↥H) (w : ↥(tildeOf Z U)) :
    ((actTilde Z U H hHN hHU h w : ↥(tildeOf Z U)) : SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨h, hHN h.2⟩ * w *
        (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨h, hHN h.2⟩)⁻¹ :=
  conjAct_coe_apply _ _ _

end Action
end S143
end CFSG.Quasithin
end
