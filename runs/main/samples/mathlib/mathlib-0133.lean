@[expose] public section

noncomputable section

open DirectSum

open DirectSum SetLike

variable {ι A σ : Type*}

variable [CommRing A] [SetLike σ A]

local notation "at " x => Localization x

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

section mapAway

variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]

variable (𝒜 : ι → σ) [GradedRing 𝒜]

variable {e : ι} {f : A} {g : A} (hg : g ∈ 𝒜 e) {x : A} (hx : x = f * g)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
lemma awayMapAux_mk (n a i hi) :
    awayMapAux 𝒜 ⟨_, hx⟩ (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩) =
      Localization.mk (a * g ^ i) ⟨x ^ i, (Submonoid.mem_powers_iff _ _).mpr ⟨i, rfl⟩⟩ := by
  have : algebraMap A (Localization.Away x) f *
    (Localization.mk g ⟨f * g, (Submonoid.mem_powers_iff _ _).mpr ⟨1, by simp [hx]⟩⟩) = 1 := by
    rw [← Algebra.smul_def, Localization.smul_mk]
    exact Localization.mk_self ⟨f*g, _⟩
  simp only [awayMapAux, RingHom.coe_comp, Function.comp_apply, algebraMap_apply, val_mk]
  rw [Localization.awayLift_mk (hv := this), ← Algebra.smul_def,
    Localization.mk_pow, Localization.smul_mk]
  subst hx
  rfl

end mapAway
end HomogeneousLocalization
end
end
