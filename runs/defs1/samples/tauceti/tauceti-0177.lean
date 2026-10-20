public section

open scoped TensorProduct

universe u v

namespace Subalgebra

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- A subalgebra `A` of a Hopf algebra `H` is a **Hopf subalgebra** when comultiplication maps it
into the image of `A ⊗[R] A` and the antipode maps it into itself. -/
structure IsHopfSubalgebra (A : Subalgebra R H) : Prop where
  /-- The comultiplication of an element of `A` lies in the image of `A ⊗[R] A`. -/
  comul_mem ⦃x : H⦄ : x ∈ A →
    Coalgebra.comul (R := R) x ∈
      LinearMap.range (TensorProduct.map (toSubmodule A).subtype (toSubmodule A).subtype)
  /-- The antipode maps `A` into itself. -/
  antipode_mem ⦃x : H⦄ : x ∈ A → HopfAlgebra.antipode R x ∈ A

end Subalgebra
end
