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

/-- The vertex module, defined as the cokernel of the incoming-arrow map. -/
abbrev signlessPreprojectiveVertexModule (v : R) :=
  signlessPreprojectiveRightProjective k v ⧸ LinearMap.range (signlessPreprojectiveKoszulRight k v)

end Reverse
end TauCeti
end
