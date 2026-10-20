@[expose] public section

universe uR uS uT uM uN uP

namespace LinearMap

section Semiring

variable {R : Type uR} {S : Type uS} {T : Type uT}

variable {M : Type uM} {N : Type uN} {P : Type uP}

variable [Semiring R] [Semiring S] [Semiring T]

variable [AddCommGroup M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module S N] [Module T P]

variable {σ : R →+* S} {ρ : R →+* T} {τ : S →+* T}

variable [RingHomSurjective σ] [RingHomCompTriple σ τ ρ]

/-- Descend `g` along a surjective `f` when `g` kills the kernel of `f`.
The underlying function is the extension of `g` along `f`, with zero as its
value outside the range. -/
noncomputable def liftOfSurjective (f : M →ₛₗ[σ] N) (hf : Function.Surjective f)
    (g : M →ₛₗ[ρ] P) (hker : f.ker ≤ g.ker) : N →ₛₗ[τ] P where
  toFun := Function.extend f g 0
  map_add' := by
    have hfg := factorsThrough_of_ker_le_ker f g hker
    intro x y
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← f.map_add, hfg.extend_apply, hfg.extend_apply, hfg.extend_apply, g.map_add]
  map_smul' := by
    have hfg := factorsThrough_of_ker_le_ker f g hker
    intro c y
    obtain ⟨r, rfl⟩ := σ.surjective c
    obtain ⟨x, rfl⟩ := hf y
    rw [← f.map_smulₛₗ, hfg.extend_apply, hfg.extend_apply, g.map_smulₛₗ,
      RingHomCompTriple.comp_apply]

end Semiring
end LinearMap
end
