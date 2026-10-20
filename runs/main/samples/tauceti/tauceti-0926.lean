public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField

open scoped AdicCompletionExtension Pointwise

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [Algebra K L]

variable {K L} [NumberField L] [IsGalois K L]

section Decomposition

variable (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

theorem localArtinAt_eq_one_iff_mem_normGroup [IsMulCommutative Gal(L/K)]
    (x : (v.adicCompletion K)ˣ) :
    localArtinAt K L v x = 1 ↔ x ∈ normGroup (v.adicCompletion K) (w.adicCompletion L) := by
  set φ := (MulAction.stabilizer Gal(L/K) w.asIdeal).subtype.comp
    (HeightOneSpectrum.decompositionEquiv v w).symm.toMonoidHom
  -- `Gal(L_w/K_v)^ab → Gal(L/K)^ab` is injective: `Gal(L/K)` is commutative, so it is its own
  -- abelianization, and `Gal(L_w/K_v)` embeds in it as the decomposition group.
  have hφ : ∀ z, Abelianization.map φ z = 1 → z = 1 := fun z ↦ by
    induction z using QuotientGroup.induction_on with
    | H ρ =>
      intro h
      have h' : φ ρ ∈ (Abelianization.of (G := Gal(L/K))).ker :=
        MonoidHom.mem_ker.2 (by rwa [← Abelianization.map_of])
      rw [Abelianization.ker_of, commutator_eq_bot, Subgroup.mem_bot] at h'
      have hρ : ρ = 1 := (HeightOneSpectrum.decompositionEquiv v w).symm.injective <|
        Subtype.ext (by simpa [φ] using h')
      rw [hρ]
      exact map_one (Abelianization.of (G := Gal(w.adicCompletion L/v.adicCompletion K)))
  rw [localArtinAt_eq_map_normResidue v w]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [(QuotientGroup.eq_one_iff x).2 h, map_one, map_one]⟩
  rw [← QuotientGroup.eq_one_iff, ← (normResidue _ _).map_eq_one_iff]
  exact hφ _ h

end Decomposition
end TauCeti.ClassFieldTheory
end
end
