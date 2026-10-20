public section

namespace TauCeti

open _root_.Quiver PathAlgebra MulOpposite CategoryTheory

universe u v w

variable (k : Type w) [CommRing k] {R : Type u} [Quiver.{v} R]
  [Finite R] [∀ x : R, Fintype (Quiver.Star x)]

noncomputable local instance signlessResolutionFintypeVertex : Fintype R := Fintype.ofFinite R

noncomputable local instance signlessResolutionFintypeArrow (i j : R) : Fintype (i ⟶ j) := by
  letI : Finite (i ⟶ j) :=
    Finite.of_injective (fun b : i ⟶ j => (Quiver.Star.mk b : Quiver.Star i)) sigma_mk_injective
  exact Fintype.ofFinite _

section Reverse

variable [HasReverse R]

local notation "Π" => signlessPreprojectiveAlgebra k R

local notation "π" => signlessPreprojectiveMk k R

local notation "e" => fun i : R => π (vertexIdempotent k i)

/-- The underlying coefficient module of the right vertex module is one copy of `k`,
identified by its vertex coefficient. -/
noncomputable def signlessPreprojectiveVertexModuleEquiv (v : R) :
    signlessPreprojectiveVertexModule k v ≃ₗ[k] k :=
  (Submodule.Quotient.restrictScalarsEquiv k
    (LinearMap.range (signlessPreprojectiveKoszulRight k v))).symm.trans
    ((Submodule.quotEquivOfEq _ _
      (range_signlessKoszulRight_restrictScalars_eq_ker_coeff k v)).trans
      ((signlessVertexCoeff k v).quotKerEquivOfSurjective (signlessVertexCoeff_surjective k v)))

end Reverse
end TauCeti
end
