public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_13 {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h157 : Lemma1517Concl T Mc M) (h159 : Lemma1519Concl T Mc M)
    (h1512 : ∀ H : Subgroup G, IsHStar T M H →
      ⁅omegaOneCenterOf (thompsonJi T 1), oTwoUpper H⁆ = ⊥)
    (h3 : Lemma15113Three T Mc M) (h4 : Lemma15113Four T Mc M) : Lemma15113Concl T Mc M :=
  ⟨lemma_15_1_13_one h hM h1512, lemma_15_1_13_two h hM h157 h159 (lemma_15_1_13_one h hM h1512),
    h3, h4⟩

end CFSG.Quasithin
end
