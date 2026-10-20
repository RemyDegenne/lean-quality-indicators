public section

open Module

namespace TauCeti.IntegralLattice

universe u

theorem exists_finset_forall_exists_gramMatrix_mem (n : ℕ) (D : ℤ) :
    ∃ S : Finset (Matrix (Fin n) (Fin n) ℤ), ∀ {V : Type u} [AddCommGroup V] [Module ℚ V]
      (L : IntegralLattice V), L.IsPosDef → finrank ℤ L = n → L.determinant ≤ D →
        ∃ b : Basis (Fin n) ℤ L, L.gramMatrix b ∈ S := by
  obtain ⟨S, hS⟩ := LinearMap.BilinForm.exists_finset_forall_exists_toMatrix_mem.{u} n D
  refine ⟨S, fun {V} _ _ L hL hn hD ↦ ?_⟩
  let b := Module.finBasisOfFinrankEq ℤ L hn
  rw [L.determinant_eq_gramDet b, gramDet_def, gramMatrix_eq_toMatrix] at hD
  obtain ⟨c, hc⟩ := hS L.integralForm L.isSymm_integralForm
    (fun x hx ↦ by simpa [integralNorm_apply] using hL.posDef_integralNorm x hx) b hD
  exact ⟨c, by rwa [gramMatrix_eq_toMatrix]⟩

end TauCeti.IntegralLattice
end
