public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Base

variable {G : Type} [Group G] [Finite G]

namespace S2Base

variable {T M H S L D : Subgroup G} {n : ℕ} {t : G} {M₀ : Subgroup G} {x₀ : G} {q : ℕ}
  {W : Subgroup G} (B : S2Base T M H S L D n t M₀ x₀ q W)

include B

theorem dbl : AppE.Dbl T M H S L n t := B.su.D

end S2Base
end Base
end CFSG.QuasithinUnique.Lin2
end
