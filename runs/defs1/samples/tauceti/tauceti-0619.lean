public section

open scoped Nat

namespace TauCeti

namespace StandardYoungTableau

variable {μ : YoungDiagram}

/-- The **row-superstandard tableau** of `μ`: the standard Young tableau numbering the cells of
`μ` in reading order, left to right along the first row, then left to right along the second, and
so on.  This is the tableau at which the classical-groups roadmap fixes the Young symmetrizer
`c_λ`. -/
noncomputable def rowSuperstandard (μ : YoungDiagram) : StandardYoungTableau μ where
  toTableau :=
    Equiv.ofBijective
      (fun c => ⟨YoungDiagram.readingIndex μ c.1, YoungDiagram.readingIndex_lt_card c.2⟩)
      ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨fun c d hcd =>
          Subtype.ext (YoungDiagram.eq_of_readingIndex_eq c.2 d.2 (congrArg Fin.val hcd)),
          by simp⟩)
  row_strict' := fun {i j₁ j₂} h _ =>
    Fin.lt_def.mpr (YoungDiagram.readingIndex_lt_readingIndex_of_snd_lt
      (μ := μ) (c := (i, j₁)) (d := (i, j₂)) rfl h)
  col_strict' := fun {i₁ i₂ j} h hcell =>
    Fin.lt_def.mpr (YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt
      (c := (i₁, j)) (d := (i₂, j)) (μ.up_left_mem h.le (le_refl j) hcell) h)

end StandardYoungTableau
end TauCeti
end
