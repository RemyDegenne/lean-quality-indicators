@[expose] public section

universe uR uP uL uM uN

namespace LinearMap

variable {R : Type uR} [Semiring R]

variable {P : Type uP} {L : Type uL} {M : Type uM} {N : Type uN}

variable [AddCommMonoid P] [AddCommMonoid L] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R P] [Module R L] [Module R M] [Module R N]

theorem postcomp_injective (i : L →ₗ[R] M) (hi : Function.Injective i) :
    Function.Injective (postcomp (P := P) i) :=
  hi.injective_linearMapComp_left

end LinearMap
end
