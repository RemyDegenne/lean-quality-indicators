public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)

/-- Canonical equivalence from the localized module over `Localization.Away f`
to native sections on `D(f)`. It is semilinear over the native
`IsLocalization.algEquiv` from `Away f` to `Γ(Spec R, D(f))`. -/
noncomputable def awayModuleEquiv (L : ModuleCat.{u} R) (f : R) :
    letI : RingHomInvPair
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv.toRingHom
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).symm.toRingEquiv.toRingHom :=
      RingHomInvPair.of_ringEquiv
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv
    letI : RingHomInvPair
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).symm.toRingEquiv.toRingHom
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv.toRingHom :=
      RingHomInvPair.of_ringEquiv_symm
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv
    LinearEquiv (σ' := (IsLocalization.algEquiv (.powers f) (Localization.Away f)
        Γ(Spec R, PrimeSpectrum.basicOpen f)).symm.toRingEquiv.toRingHom)
      (IsLocalization.algEquiv (.powers f) (Localization.Away f)
        Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv.toRingHom
      (LocalizedModule (.powers f) L) Γ(tilde L, PrimeSpectrum.basicOpen f) := by
  letI : Module Γ(Spec R, PrimeSpectrum.basicOpen f)
      (LocalizedModule (.powers f) L) := LocalizedModule.moduleOfIsLocalization
  let e₀ := IsLocalizedModule.iso (.powers f)
    (tilde.toOpen L (PrimeSpectrum.basicOpen f)).hom
  let e : LocalizedModule (.powers f) L ≃ₗ[R] Γ(tilde L, PrimeSpectrum.basicOpen f) := e₀
  let eS := e.extendScalarsOfIsLocalization (.powers f)
    Γ(Spec R, PrimeSpectrum.basicOpen f)
  exact
    { e.toAddEquiv with
      map_smul' := fun r x ↦ by
        change eS (r • x) = IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f) r • eS x
        rw [away_smul_eq_native R L f r x, eS.map_smul] }

end AlgebraicGeometry.Scheme.Modules
end
end
