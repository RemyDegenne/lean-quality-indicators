public noncomputable section

open IsDedekindDomain NumberField

open scoped AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

variable (K : Type) (L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

theorem auxiliaryKummerIdeleSubgroup_le_range_ideleNormMap {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, v ∉ S →
      ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (hU : ∀ v ∉ S, v ∉ T →
      ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) :
    auxiliaryKummerIdeleSubgroup S T n ≤
      (GlobalNumberFields.ideleNormMap K L).toMonoidHom.range := by
  intro x hx
  rw [mem_auxiliaryKummerIdeleSubgroup_iff] at hx
  refine mem_range_ideleNormMap_of_exponent_dvd K L hn
    (S := (S : Set _)) (T := (T : Set _) \ (S : Set _)) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    exact hT v hv.1 hv.2
  · intro v hvS hvT
    exact hU v hvS fun hv ↦ hvT ⟨hv, hvS⟩
  · intro v hv
    rw [powerSubgroup_eq_range_powMonoidHom]
    exact hx.1 v hv
  · intro v hvS hvT
    exact hx.2.2 v hvS fun hv ↦ hvT ⟨hv, hvS⟩
  · intro w
    rw [powerSubgroup_eq_range_powMonoidHom]
    exact hx.2.1 w

end TauCeti.ClassFieldTheory
end
