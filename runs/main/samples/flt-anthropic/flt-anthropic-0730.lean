namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_sectionsOf_equiv_lineBundle_one_add_of_pullback_quotient_isNilpotent

set_option autoImplicit false

universe u

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

set_option quotPrecheck false

namespace P2mDker

section Main

variable {A : Type u} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J)
  {X : Scheme.{u}} (c : X ⟶ Spec (.of A)) (𝒱 : X.TwoAffineOpenCover)
  {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
  (h : Nonempty ((Scheme.Modules.pullback
      (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))).obj L ≅
    SheafOfModules.unit (Limits.pullback c (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).ringCatSheaf))

local notation "A'" => A ⧸ J

local notation "XJ" => Limits.pullback c (Scheme.TwoAffineOpenCover.specMap A (A ⧸ J))

local notation "pJ" => Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap A (A ⧸ J))

local notation "qJ" => Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap A (A ⧸ J))

local notation "𝒱J" => Scheme.TwoAffineOpenCover.pullback 𝒱 c (A ⧸ J)

local notation "𝒰" => Scheme.TwoAffineOpenCover.cover 𝒱 c

local notation "𝒰J" => Scheme.TwoAffineOpenCover.cover (Scheme.TwoAffineOpenCover.pullback 𝒱 c (A ⧸ J))
  (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap A (A ⧸ J)))

local notation "S" => Scheme.TwoAffineOpenCover.sectionsOf 𝒱 c L

local notation "LJ" => (Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap A (A ⧸ J)))).obj L

local notation "SJ" => Scheme.TwoAffineOpenCover.sectionsOf (Scheme.TwoAffineOpenCover.pullback 𝒱 c (A ⧸ J))
  (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap A (A ⧸ J)))
  ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap A (A ⧸ J)))).obj L)

local notation "σ0" => CommRingCat.Hom.hom (Scheme.Hom.app
  (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap A (A ⧸ J))) 𝒱.U0)

local notation "σ1" => CommRingCat.Hom.hom (Scheme.Hom.app
  (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap A (A ⧸ J))) 𝒱.U1)

local notation "σ01" => CommRingCat.Hom.hom (Scheme.Hom.app
  (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap A (A ⧸ J))) (𝒱.U0 ⊓ 𝒱.U1))

local notation "I[" B "]" => Ideal.map (algebraMap A B) J

theorem chart_facts {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A B] [Algebra (A ⧸ J) B']
    (e : (A' ⊗[A] B) ≃ₐ[A'] B') (σ : B →+* B') (he : ∀ s, e ((1 : A') ⊗ₜ[A] s) = σ s) :
    Function.Surjective σ ∧ (∀ b, σ b = 0 → b ∈ I[B]) := by
  constructor
  · intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨b, rfl⟩ := TensorProduct.mk_surjective A B (A ⧸ J) Ideal.Quotient.mk_surjective z
    exact ⟨b, (he b).symm⟩
  · intro b hb
    rw [← he, EmbeddingLike.map_eq_zero_iff] at hb
    have hb' : b ∈ J • (⊤ : Submodule A B) := mem_smul_top_of_tmul_eq_zero J hb
    have := smul_top_le (B := B) (M := B) J hb'
    rwa [Ideal.smul_eq_mul, Ideal.mul_top] at this

end Main
end P2mDker
end
end P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_sectionsOf_equiv_lineBundle_one_add_of_pullback_quotient_isNilpotent
