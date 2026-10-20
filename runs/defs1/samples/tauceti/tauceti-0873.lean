public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

variable {I : Type w} {κ : Type} [Finite κ]

variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)

variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)

variable (M : AddSubgroup V)

variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)

variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

variable (wt : Fin n → κ → ℤ)

/-- The `i`th represented root subgroup on algebra-valued points of the toral Kostant closure.

Its coordinate morphism is `kostantRootSubgroupToralCoordinateMap`; contravariance of the functor
of points turns that morphism into a homomorphism from the additive-group points to the intrinsic
points of the quotient coordinate Hopf algebra. -/
noncomputable def kostantRootSubgroupToralPoints (i : I) (A : CommAlgCat.{v} ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) A →*
      HopfAlgebra.points
        (R := ℤ)
        (H := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralDefiningIdeal e h ρ M hM hnil b wt)) A :=
  ((CommHopfAlgCat.Hom.mapPointsFunctor
    (kostantRootSubgroupToralCoordinateMap e h ρ M hM hnil b wt i)).app A).hom

end TauCeti.UniversalEnvelopingAlgebra
end
