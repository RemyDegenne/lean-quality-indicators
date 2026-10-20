@[expose] public section

universe u v w

namespace Ideal

open Function RingHom

variable {R : Type u} {S : Type v} {F : Type w} [Ring R] [Semiring S]

section QuotientAlgebra

variable (R₁ R₂ : Type*) {A B : Type*}

variable [CommSemiring R₁] [CommSemiring R₂] [Ring A]

variable [Algebra R₁ A] [Algebra R₂ A]

lemma Quotient.mk_bijective_iff_eq_bot (I : Ideal A) [I.IsTwoSided] :
    Function.Bijective (mk I) ↔ I = ⊥ := by
  constructor
  · intro h
    rw [← map_eq_bot_iff_of_injective h.1]
    exact (map_eq_bot_iff_le_ker _).mpr <| le_of_eq mk_ker.symm
  · exact fun h => ⟨(injective_iff_ker_eq_bot _).mpr <| by rw [mk_ker, h], mk_surjective⟩

end QuotientAlgebra
end Ideal
end
