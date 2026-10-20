public section

namespace TauCeti

namespace StandardYoungTableau

@[simp]
theorem transpose_apply_val {μ : YoungDiagram} (T : StandardYoungTableau μ)
    (c : ↥μ.transpose.cells) : (T.transpose c).val =
      (T ⟨c.1.swap, YoungDiagram.mem_transpose.mp c.2⟩).val :=
  calc
    (T.transpose c).val = (T.transpose.toTableau c).val :=
      congrArg Fin.val (toTableau_apply T.transpose c).symm
    _ = (T ⟨c.1.swap, YoungDiagram.mem_transpose.mp c.2⟩).val := by
      simp only [transpose, Equiv.trans_apply, transposeCellEquiv_apply,
        finCongr, Equiv.coe_fn_mk, Fin.val_cast, toTableau_apply]

end StandardYoungTableau
end TauCeti
end
