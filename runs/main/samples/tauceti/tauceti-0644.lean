public section

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

section Transport

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]
  {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
  [Field N] [Algebra C N] [IsFractionRing C N]

theorem exists_valuationOfNeZero_map_eq (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L)) (w : HeightOneSpectrum C)
    (hne : w.asIdeal.comap ψ ≠ ⊥) :
    ∃ e : ℕ, ∀ u : Lˣ, w.valuationOfNeZero (Units.map (φ : L →* N) u) =
      (comapOfNeBot ψ w hne).valuationOfNeZero u ^ e := by
  -- the tower of algebras that `valuation_liesOver` compares the two valuations along
  let _ : Algebra B C := ψ.toAlgebra
  let _ : Algebra L N := φ.toAlgebra
  let _ : Algebra B N := (φ.comp (algebraMap B L)).toAlgebra
  have hψ : Function.Injective ψ := .of_comp (f := algebraMap C N) <| by
    rw [← RingHom.coe_comp, hcomp]
    exact φ.injective.comp (IsFractionRing.injective B L)
  have : IsScalarTower B L N := .of_algebraMap_eq' rfl
  have : IsScalarTower B C N := .of_algebraMap_eq' hcomp.symm
  have : Module.IsTorsionFree B C := Module.isTorsionFree_iff_algebraMap_injective.mpr hψ
  have : w.asIdeal.LiesOver (comapOfNeBot ψ w hne).asIdeal := ⟨comapOfNeBot_asIdeal ψ w hne⟩
  refine ⟨w.asIdeal.ramificationIdx B, fun u ↦ ?_⟩
  rw [valuationOfNeZero_eq_iff, WithZero.coe_pow, valuationOfNeZero_eq]
  exact (valuation_liesOver N (comapOfNeBot ψ w hne) w (u : L)).symm

end Transport
end IsDedekindDomain.HeightOneSpectrum
end
