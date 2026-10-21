namespace OAI

noncomputable section

open Set Metric Topology BigOperators

open Set Metric Topology

open Set Topology

open Set Metric Topology

open scoped NNReal

open Set Metric Topology

open scoped NNReal ENNReal

open Set Metric Topology

open scoped TensorProduct

namespace UniversalFInfinity.Simplicial

section

open Set Metric Topology BigOperators

open scoped Classical unitInterval

universe u v

variable {V : Type u} {W : Type v}

variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

variable (p : V × V → W) (hp : ∀ s t : Face K, (s.1 ×ˢ t.1).image p ∈ L)

variable [Finite (Face K)]

lemma productDiagonal_carried (s : Face K) (x : Space K) (hx : x.1.support ⊆ s.1) :
    (productDiagonal K L p hp x).1.support ⊆ (diagonalCarrier K L p hp s).1 :=
  (pairMap_support K K L p hp x x).trans (Finset.image_subset_image (Finset.product_subset_product hx hx))

end
end UniversalFInfinity.Simplicial
end
end OAI
