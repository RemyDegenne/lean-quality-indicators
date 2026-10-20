set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section FieldComparison

variable {k : Type u} [Field k]

@[simp] lemma RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (D : AlgebraicCurve.RelEffDivisor C c r T t)
    (h : LocallyOfFinitePresentation (D.I.subschemeι ≫ pullback.snd c t)) :
    (RelEffCartierDiv.ofRelEffDivisor D h).toRelEffDivisor = D := rfl

end FieldComparison
end AlgebraicGeometry
