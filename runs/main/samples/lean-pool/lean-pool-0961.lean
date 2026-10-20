public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol

open NFChoice.Foundation.ExactLiteralTrial

open NFChoice.SemanticCore

open NFChoice.SemanticCore.Lowering

open NFChoice.Compiler.NFCompactLeafSemanticAdapters

open NFChoice.Compiler.NFCompactLeafEndpoints

section StratificationSupport

theorem stratifiedBy_renameVars {n m : Nat} (rho : Fin n → Fin m) (smallTy : Fin n → Int)
    (largeTy : Fin m → Int) (hTy : ∀ i, largeTy (rho i) = smallTy i) (p : Formula n)
    (hp : Formula.StratifiedBy smallTy p) :
    Formula.StratifiedBy largeTy (ExactLiteralTrial.Formula.renameVars rho p) := by
  induction p generalizing m largeTy with
  | falsum => trivial
  | equal i j =>
    simpa [ExactLiteralTrial.Formula.renameVars, Formula.StratifiedBy, hTy i, hTy j] using
      hp
  | mem i j =>
    simpa [ExactLiteralTrial.Formula.renameVars, Formula.StratifiedBy, hTy i, hTy j] using
      hp
  | imp p q ihp ihq =>
    constructor
    · apply ihp
      · exact hTy
      · exact hp.1
    · apply ihq
      · exact hTy
      · exact hp.2
  | all p ih =>
    rcases hp with ⟨k, hp⟩
    refine ⟨k, ?_⟩
    apply
      ih (Fin.cases 0 (fun i => Fin.succ (rho i))) (Fin.cases k smallTy)
        (Fin.cases k largeTy)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact hTy j
    · exact hp

end StratificationSupport
end NFChoice.Foundation.NFStandard
end
