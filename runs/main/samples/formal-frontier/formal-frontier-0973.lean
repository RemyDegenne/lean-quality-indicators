@[expose] public section

noncomputable section

universe u v w x y

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

variable {M : Type v} [AddCommGroup M] [Module R M]

variable {N : Type w} [AddCommGroup N] [Module R N]

@[simp]
theorem precompOfLinearEquiv_toLinearMap [IsAdicComplete I N] (hI : I.FG) :
    (precompOfLinearEquiv I (M := M) (N := N) hI).toLinearMap =
      LinearMap.lcomp R N (of I M) :=
  rfl

end AdicCompletion
end
end
