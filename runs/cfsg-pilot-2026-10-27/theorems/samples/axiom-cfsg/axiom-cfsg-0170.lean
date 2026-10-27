public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

open scoped commutatorElement

section Stage68

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

omit [Finite G] in
theorem Y_le_normalizer_YE (h1 : Case157One T Mc M) (L : LineData153 T M V₁ V₂ E) :
    Y153 Mc M ≤ Subgroup.normalizer (YE153 Mc M E : Set G) :=
  (Y_le_normalizer_NY h1 L).trans (normalizer_le_normalizer_oTwoUpper _)

end Stage68
end CFSG.Quasithin
end
