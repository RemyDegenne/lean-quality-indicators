public section

open Function Set

open CategoryTheory

universe u v w

namespace Module

variable {R : Type u} [CommRing R]

theorem componentwiseFreeModel_projective {I : Type*} [Finite I]
    (e : I → R) (n : I → ℕ) (he : ∀ i, IsIdempotentElem (e i)) :
    Module.Projective R (ComponentwiseFreeModel e n) := by
  let _ : Fintype I := Fintype.ofFinite I
  let _ (i : I) (k : Fin (n i)) : Module.Projective R (Ideal.span {e i}) :=
    (he i).projective_span
  let _ (i : I) : Module.Projective R (Fin (n i) → Ideal.span {e i}) :=
    Module.Projective.of_equiv'
      (DirectSum.linearEquivFunOnFintype R (Fin (n i)) fun _ ↦ Ideal.span {e i})
  exact Module.Projective.of_equiv'
    (DirectSum.linearEquivFunOnFintype R I fun i ↦
      (k : Fin (n i)) → Ideal.span {e i})

end Module
end
