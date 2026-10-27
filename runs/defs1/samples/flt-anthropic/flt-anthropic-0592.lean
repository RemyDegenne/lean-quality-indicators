namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TrivSqZeroExt NeronModelInfra GoodReductionJacobian

namespace BTDim

noncomputable section

p2m_reactivate

p2m_reactivate

section Bridge

variable {R : Type} [CommRing R] [IsLocalRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
  {L : RelativeGroupLaw R f} {p h : ℕ} {G : PDivisibleGroup R p h}
  (e : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T],
    G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v))
  (he_mul : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x y : G.Point T v),
    ((e v T (x * y)).val : SchemeHomOver _ f) = L.mul _ (e v T x).val (e v T y).val)
  (he_nat : ∀ (v : ℕ) (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (x : G.Point T v),
    ((e v T' (G.pointMap a v x)).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e v T x).val.1)
  {v : ℕ}
  {M : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  {N : Type} [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]

variable (L) (p) (v) in

abbrev KJ : Submodule R (ωJ L) := Ideal.span {(p : R) ^ v} • ⊤

end Bridge
end
end BTDim
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension
