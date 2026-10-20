namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_forall_map_eq_of_span_eq_top

set_option autoImplicit false

open scoped TensorProduct

open TensorProduct LT.LatticeTree CerednikDrinfeld.FormalOmega

namespace OmegaGlueSol

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

variable {B : Type} [CommRing B] [Algebra 𝒪 B]

section Glue

variable {n : ℕ} (f : Fin n → B)
  (L : Fin n → Type) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)] [∀ i, Algebra 𝒪 (L i)]
  [∀ i, IsScalarTower 𝒪 B (L i)] [∀ i, IsLocalization.Away (f i) (L i)]
  (π : 𝒪) (x : ∀ i, OmegaObj (K := K) π (L i))

noncomputable def glueLine (M : FullLattice 𝒪 K) : Submodule B (latticeBaseChange 𝒪 K B M) :=
  ⨅ i, (((x i).line M).restrictScalars B).comap (bcMap (L i) M)

end Glue
end OmegaGlueSol
end P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_forall_map_eq_of_span_eq_top
