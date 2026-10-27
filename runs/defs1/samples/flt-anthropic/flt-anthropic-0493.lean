set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {k : Type u} [Field k]

noncomputable def RelEffDivisor.pullbackAlong {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) : RelEffDivisor C c r T t where
  I := Dcan.I.comap (mapOnProd c φ hφ)
  isFinite :=
    have := Dcan.isFinite
    MorphismProperty.of_isPullback (isPullback_comap_snd Dcan.I φ hφ) ‹_›
  flat :=
    have := Dcan.flat
    MorphismProperty.of_isPullback (isPullback_comap_snd Dcan.I φ hφ) ‹_›
  finrank_eq s := by
    have := Dcan.isFinite
    have := Dcan.flat
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_comap_snd Dcan.I φ hφ) s]
    exact Dcan.finrank_eq (φ s)

end AlgebraicCurve
