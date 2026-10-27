public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits

open scoped commutatorElement Pointwise

namespace S153E56e

open CFSG.Quasithin.S153E

section PartA

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t}

theorem U'_le_centralizer_Z' (cx : Ctx15350 T Mc M V₁ V₂ t) (y : G) :
    conjSubgroup (UH153 T M V₁ Mc) y ≤
      Subgroup.centralizer (conjSubgroup (quasithinOmegaOneCenter T) y : Set G) :=
  (conjSubgroup_mono (U_le_centralizer_Z cx) y).trans (conjSubgroup_centralizer _ y).le

end PartA
end S153E56e
end CFSG.Quasithin
end
