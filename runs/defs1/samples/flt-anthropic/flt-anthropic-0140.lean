namespace P2MW.S_Algebra_nonempty_patchingDatum_of_levelData

set_option autoImplicit false

namespace M4cP4Glue

open IsLocalRing MvPowerSeries MonoidAlgebra

section Delta

variable (𝒪 : Type) [CommRing 𝒪] (p : ℕ) {r : ℕ} (kk : Fin r → ℕ)

abbrev Lam : Type := MonoidAlgebra 𝒪 (Delta p kk)

end Delta
end M4cP4Glue
end P2MW.S_Algebra_nonempty_patchingDatum_of_levelData
