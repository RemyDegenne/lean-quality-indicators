public section

namespace CFSG.AGLEmbeddingD2.ParabLevi

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LieOut

open scoped commutatorElement

variable {K : Type*} [Group K]

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
  {I : Set (Fin D.rank)}

theorem radical_le_leviRad {j : Fin D.rank} (hj : j ∉ I) : radical D j ≤ leviRad D I :=
  le_iSup₂_of_le (f := fun j (_ : j ∈ Iᶜ) => radical D j) j hj le_rfl

end CFSG.AGLEmbeddingD2.ParabLevi
end
