namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (S : Finset B) :
    ∃ U : B.Opens, IsAffineOpen U ∧ ∀ b ∈ S, b ∈ U := by

  obtain ⟨U, hU₁, hU₂⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing g

  exact GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing
    LB U hU₁ hU₂ S

end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing
