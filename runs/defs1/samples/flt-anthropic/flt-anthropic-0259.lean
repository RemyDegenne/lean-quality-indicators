set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicCurve

open AlgebraicGeometry

structure SymmetricPowerPackage {k : Type u} [Field k] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ) where

  Csym : Scheme.{u}

  csym : Csym ⟶ Spec (CommRingCat.of k)

  π : finFibrePow c r ⟶ Csym

  π_comp_csym : π ≫ csym = finFibrePow.toBase c r

  permAct_comp_π : ∀ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).hom ≫ π = π

  isFinite_π : IsFinite π

  surjective_π : Surjective π

  π_apply_eq_iff : ∀ x x' : ↥(finFibrePow c r),
    π.base x = π.base x' ↔ ∃ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).hom.base x = x'

  app_injective : ∀ V : Csym.Opens, Function.Injective (π.app V)

  range_app : ∀ V : Csym.Opens, Set.range (π.app V) =
    {s | ∀ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
      (le_preimage_of_comp_eq _ _ (permAct_comp_π σ) V) s = s}

  exists_affine_chart : ∀ U : C.Opens, IsAffineOpen U →
    ∃ V : Csym.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = ⨅ l : Fin r, (finFibrePow.proj c r l) ⁻¹ᵁ U

  integral : IsIntegral Csym

  proper : IsProper csym

  smooth : SmoothOfRelativeDimension r csym

end AlgebraicCurve
