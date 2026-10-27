public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C)

namespace FiniteResolution

variable {E} {P : ObjectProperty C}

section Biprod

variable [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderBinaryProducts]

/-- The componentwise direct sum of two finite `P`-resolutions. Where one chain has run out, it
is padded against the other by the trivial conflation on its last syzygy. -/
noncomputable def biprod :
    ∀ {X Y : C}, FiniteResolution E P X → FiniteResolution E P Y →
      FiniteResolution E P (X ⊞ Y)
  | _, _, .base hX, .base hY =>
      .base (P.prop_biprod_of_isClosedUnderBinaryProducts hX hY)
  | X, _, .base hX, .step hQ i p zero hp s =>
      .step (P.prop_biprod_of_isClosedUnderBinaryProducts hX hQ)
        (Limits.biprod.map (0 : (0 : C) ⟶ X) i) (Limits.biprod.map (𝟙 X) p)
        (by apply Limits.biprod.hom_ext' <;> simp [reassoc_of% zero])
        (E.conflation_biprod (E.conflation_zero_id X) hp)
        (s.ofIso (isoZeroBiprod (isZero_zero C)))
  | _, Y, .step hQ i p zero hp r, .base hY =>
      .step (P.prop_biprod_of_isClosedUnderBinaryProducts hQ hY)
        (Limits.biprod.map i (0 : (0 : C) ⟶ Y)) (Limits.biprod.map p (𝟙 Y))
        (by apply Limits.biprod.hom_ext' <;> simp [reassoc_of% zero])
        (E.conflation_biprod hp (E.conflation_zero_id Y))
        (r.ofIso (isoBiprodZero (isZero_zero C)))
  | _, _, .step hQ i p zero hp r, .step hQ' i' p' zero' hp' s =>
      .step (P.prop_biprod_of_isClosedUnderBinaryProducts hQ hQ')
        (Limits.biprod.map i i') (Limits.biprod.map p p')
        (by apply Limits.biprod.hom_ext' <;> simp [reassoc_of% zero, reassoc_of% zero'])
        (E.conflation_biprod hp hp') (r.biprod s)

end Biprod
end FiniteResolution
end ExactStructure
end TauCeti
end
