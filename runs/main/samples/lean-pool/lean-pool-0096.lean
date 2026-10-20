public section

namespace NFChoice.Compiler.NFCompactLeafFinalGate

open scoped Fol

open NFChoice.Foundation

open NFChoice.Foundation.ExactLiteralTrial

open NFChoice.SemanticCore

open NFChoice.SemanticCore.Lowering

open NFChoice.Compiler.CompactSourceSyntax

open NFChoice.Compiler.NFCompactLeafEndpoints

theorem axSiCompact {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z w : Var) (hxy : x ≠ y)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    Wff.Valid S
      (synWex y (.all z (.all w
            (synWb (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (.cv y))
              (.classMem (synCopk (.cv z) (.cv w)) (.cv x)))))) :=
  by
  have hExt := NFChoice.ReplaySupport.extensional_of_literal_model hNF
  have hLit : FormulaHolds S DVec.nil literalAxSi :=
    (formulaHolds_toFlypitch DVec.nil literalAxSi).2
      (NFChoice.ReplaySupport.realizes_literal_axiom hNF .axSi)
  intro v
  apply Wff.holds_ex.mpr
  rcases formulaHolds_ex.mp (hLit (v x)) with ⟨Y, hY⟩
  refine ⟨Y, ?_⟩
  intro Z W
  apply Wff.holds_biimp.mpr
  have hiff := formulaHolds_biimp.mp (hY Z W)
  let v' := update (update (update v y Y) z Z) w W
  let xs := DVec.cons W (DVec.cons Z (DVec.cons Y (DVec.cons (v x) DVec.nil)))
  have hz : v' z = lookup xs (1 : Fin 4) :=
    by
    simp only [ne_eq, hzw, not_false_eq_true, update_noteq, update_same, Nat.reduceAdd,
      Fin.isValue, v', xs]
    change Z = Z
    rfl
  have hw : v' w = lookup xs (0 : Fin 4) := by simp [v', xs]
  have hy : v' y = lookup xs (2 : Fin 4) :=
    by
    simp only [ne_eq, hyw, not_false_eq_true, update_noteq, hyz, update_same,
      Nat.reduceAdd, Fin.isValue, v', xs]
    change Y = Y
    rfl
  have hx : v' x = lookup xs (3 : Fin 4) :=
    by
    simp only [ne_eq, hxw, not_false_eq_true, update_noteq, hxz, hxy, Nat.reduceAdd,
      Fin.isValue, v', xs]
    change v x = v x
    rfl
  calc
    Wff.Holds S v' (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (.cv y)) ↔
        FormulaHolds S xs (literalSingletonPairMem 1 0 2) :=
      holds_literalSingletonPairMem hExt v' xs z w y 1 0 2 hz hw hy
    _ ↔ FormulaHolds S xs (literalPairMem 1 0 3) := by simpa [xs] using hiff
    _ ↔ Wff.Holds S v' (.classMem (synCopk (.cv z) (.cv w)) (.cv x)) :=
      (holds_literalPairMem hExt v' xs z w x 1 0 3 hz hw hx).symm

end NFChoice.Compiler.NFCompactLeafFinalGate
end
