@[expose] public section

namespace SaxlCounterexamples.EveryBase

open scoped BigOperators Pointwise

theorem permWreath_isBaseTuple_iff_colourWord
    (H Q ι V C : Type*)
    [Group H] [Group Q] [MulAction H V] [MulAction Q ι]
    {n : Nat} (code : TupleColourCode H V n C)
    (rows : Fin n → (ι → V)) :
    Saxl.IsBaseTuple (Saxl.PermWreath H Q ι) (ι → V) rows ↔
      (∀ i, Saxl.IsBaseTuple H V (fun j ↦ rows j i)) ∧
        Saxl.WordDistinguishing Q
          (fun i ↦ code.colour (fun j ↦ rows j i)) := by
  rw [permWreath_isBaseTuple_iff]
  constructor
  · rintro ⟨hcolumns, hrows⟩
    refine ⟨hcolumns, ?_⟩
    intro q hq
    apply hrows q
    intro i
    apply (code.colour_eq_iff_sameOrbit
      (hcolumns (q⁻¹ • i)) (hcolumns i)).1
    exact hq i
  · rintro ⟨hcolumns, hword⟩
    refine ⟨hcolumns, ?_⟩
    intro q hq
    apply hword q
    intro i
    apply (code.colour_eq_iff_sameOrbit
      (hcolumns (q⁻¹ • i)) (hcolumns i)).2
    exact hq i

end SaxlCounterexamples.EveryBase
end
