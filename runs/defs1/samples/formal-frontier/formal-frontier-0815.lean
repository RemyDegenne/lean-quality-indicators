public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]
  (V : Type u) [AddCommGroup V] [Module K V]
  (W : Type u) [AddCommGroup W] [Module K W]

/-- A chosen finite basis identifies the vector group with the literal product
of its one-dimensional additive group factors. Milne, *Algebraic Groups*
(2017), item 2.6 gives this group-scheme identification over a field for a
basis of size `n`; here the categorical product also includes the empty
index type. -/
def vectorGroupSchemeProductIso {i : Type u} [Finite i]
    (b : Module.Basis i K V) :
    vectorGroupScheme K V ≅ (∏ᶜ fun _ : i ↦ additiveGroupScheme K) :=
  (vectorGroupBasisFan_isLimit K V b).conePointUniqueUpToIso
    (Limits.productIsProduct fun _ : i ↦ additiveGroupScheme K)

end AlgebraicGeometry
end
end
