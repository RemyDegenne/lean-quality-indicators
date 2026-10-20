public section

namespace TauCeti

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇

variable {R : Type*} [CommRing R]

variable {L : Type u₁} {M : Type u₂} {P : Type u₃}

variable {L' : Type u₄} {M' : Type u₅} {L'' : Type u₆} {M'' : Type u₇}

variable [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable [AddCommGroup L'] [Module R L'] [AddCommGroup M'] [Module R M']

variable [AddCommGroup L''] [Module R L''] [AddCommGroup M''] [Module R M'']

variable [AddCommGroup P] [Module R P]

variable {σ : R →+* R}

section PairingMaps

variable (b : L →ₛₗ[σ] M →ₗ[R] P) (c : L' →ₛₗ[σ] M' →ₗ[R] P)

variable (f : L →ₗ[R] L') (g : M →ₗ[R] M')

theorem leftRadical_le_comap_of_surjective_of_pairing (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    leftRadical b ≤ (leftRadical c).comap f := by
  intro x hx
  rw [Submodule.mem_comap, mem_leftRadical_iff]
  intro y'
  obtain ⟨y, rfl⟩ := hg y'
  rw [hpair]
  exact (mem_leftRadical_iff b x).mp hx y

end PairingMaps
end TauCeti
end
