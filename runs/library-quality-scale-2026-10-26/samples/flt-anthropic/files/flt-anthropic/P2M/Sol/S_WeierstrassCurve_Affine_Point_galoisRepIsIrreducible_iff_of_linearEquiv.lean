import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
namespace P2MW.S_WeierstrassCurve_Affine_Point_galoisRepIsIrreducible_iff_of_linearEquiv

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_galoisRepIsIrreducible_iff_of_linearEquiv.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_Point_galoisRepIsIrreducible_iff_of_linearEquiv.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_Affine_Point_galoisRepIsIrreducible_iff_of_linearEquiv.WeierstrassCurve.Affine.Point"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.Point"
p2m_open "WeierstrassCurve"

section Torsion

variable {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
  {E₁ E₂ : WeierstrassCurve F}

namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point"
namespace Point
p2m_export "WeierstrassCurve.Affine.Point" "IsGaloisStable GaloisRepIsIrreducible"
p2m_open "WeierstrassCurve.Affine.Point WeierstrassCurve.Affine"

lemma linearEquiv_symm_smul {n : ℕ}
    (φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n)
    (hφ : ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n), φ (σ • x) = σ • φ x)
    (σ : K ≃ₐ[F] K) (y : Submodule.torsionBy ℤ (E₂⁄K).Point n) :
    φ.symm (σ • y) = σ • φ.symm y :=
  φ.injective <| by rw [LinearEquiv.apply_symm_apply, hφ, LinearEquiv.apply_symm_apply]

theorem galoisRepIsIrreducible_of_linearEquiv {n : ℕ}
    (φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n)
    (hφ : ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n), φ (σ • x) = σ • φ x)
    (h : GaloisRepIsIrreducible (K := K) F E₁ n) : GaloisRepIsIrreducible (K := K) F E₂ n := by
  obtain ⟨hnt, hirr⟩ := h
  refine ⟨φ.injective.nontrivial, fun N hN => ?_⟩
  have hst : IsGaloisStable F (N.comap φ.toLinearMap) := fun σ x hx => by
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
    rw [hφ]
    exact hN σ _ hx
  rw [← Submodule.map_comap_eq_of_surjective φ.surjective N]
  rcases hirr _ hst with h | h
  · left
    rw [h, Submodule.map_bot]
  · right
    rw [h, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr φ.surjective

theorem galoisRepIsIrreducible_iff_of_linearEquiv_dev {n : ℕ}
    (φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n)
    (hφ : ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n), φ (σ • x) = σ • φ x) :
    GaloisRepIsIrreducible (K := K) F E₁ n ↔ GaloisRepIsIrreducible (K := K) F E₂ n :=
  ⟨galoisRepIsIrreducible_of_linearEquiv φ hφ,
    galoisRepIsIrreducible_of_linearEquiv φ.symm (linearEquiv_symm_smul φ hφ)⟩

end Affine.Point

end Torsion

end WeierstrassCurve

theorem solution {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K] [DecidableEq K] {E₁ E₂ : WeierstrassCurve F} {n : ℕ} (φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n) (hφ : ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n), φ (σ • x) = σ • φ x) : GaloisRepIsIrreducible (K := K) F E₁ n ↔ GaloisRepIsIrreducible (K := K) F E₂ n :=
  ⟨WeierstrassCurve.Affine.Point.galoisRepIsIrreducible_of_linearEquiv φ hφ,
    WeierstrassCurve.Affine.Point.galoisRepIsIrreducible_of_linearEquiv φ.symm
      (WeierstrassCurve.Affine.Point.linearEquiv_symm_smul φ hφ)⟩
