@[expose] public section

universe u v

namespace Ideal

/-- Quotienting a dependent product by a product ideal is canonically
equivalent to the dependent product of the coordinate quotients. -/
noncomputable def piQuotientRingEquiv {ι : Type u} {R : ι → Type v}
    [∀ i, CommRing (R i)] (I : ∀ i, Ideal (R i)) :
    ((∀ i, R i) ⧸ Ideal.pi I) ≃+* (∀ i, (R i ⧸ I i)) :=
  (Ideal.quotEquivOfEq (ker_piQuotientMap I).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := piQuotientMap I)
      (piQuotientMap_surjective I))

end Ideal
end
