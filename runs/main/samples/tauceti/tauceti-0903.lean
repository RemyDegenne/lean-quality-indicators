public section

namespace TauCeti

universe u v

namespace GroupLike

variable (R : Type u) (H : Type v)

section Semiring

variable [CommSemiring R] [Semiring H] [Bialgebra R H]

theorem liftGroupLikeBialgHom_surjective_iff_span_eq_top :
    Function.Surjective (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H)) ↔
      Submodule.span R
          (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤ := by
  constructor
  · intro h
    rw [← range_liftGroupLikeBialgHom R H]
    apply LinearMap.range_eq_top.2
    simpa only [BialgHom.coe_toLinearMap] using h
  · intro h
    have hsurjective : Function.Surjective
        (MonoidAlgebra.liftGroupLikeBialgHom (R := R) (A := H) :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) := by
      apply LinearMap.range_eq_top.1
      rw [range_liftGroupLikeBialgHom R H]
      exact h
    simpa only [BialgHom.coe_toLinearMap] using hsurjective

end Semiring
end GroupLike
end TauCeti
end
