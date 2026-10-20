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

@[simp]
theorem liftOfSurjective_apply (f : M →ₛₗ[σ] N) (hf : Function.Surjective f)
    (g : M →ₛₗ[ρ] P) (hker : f.ker ≤ g.ker) (x : M) :
    f.liftOfSurjective (τ := τ) hf g hker (f x) = g x := by
  exact (factorsThrough_of_ker_le_ker f g hker).extend_apply 0 x

end Semiring
end LinearMap
end
